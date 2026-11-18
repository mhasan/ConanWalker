#!/usr/bin/env python3
# ConanWalker - fetch ConanCenter recipes and upstream sources for a Conan recipe's
# whole dependency chain.
# Copyright (C) 2026 Mahmud Hasan
#
# This program is free software: you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation, either version 3 of the License, or (at your option) any later
# version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
# PARTICULAR PURPOSE. See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along with
# this program (the LICENSE file). If not, see <https://www.gnu.org/licenses/>.
#
# SPDX-License-Identifier: GPL-3.0-or-later
"""
ConanWalker
===========
Open a Conan recipe (conanfile.py or conanfile.txt), pick a target folder, and
for every dependency ConanWalker creates:

    <target>/<dependency>/
        recipe/           the ConanCenter recipe (conanfile.py, conandata.yml, patches/, test_package/ ...)
        repo/             the upstream source code (git checkout of the tag, or the extracted archive)
        dependency.json   what was resolved and where it came from

Recipes are fetched from conan-center-index on GitHub, either with a sparse git
clone (cached in ~/.conanwalker, recommended) or over the GitHub REST API.

Run with no arguments for the GUI, or headless:
    python conanwalker.py --cli path/to/conanfile.py path/to/target [--no-transitive] ...
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import queue
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Optional

try:
    import yaml
except ImportError:  # reported nicely at runtime
    yaml = None

APP_NAME = "ConanWalker"
APP_VERSION = "1.2.0"
DEVELOPER = "Mahmud Hasan"
COPYRIGHT = "Copyright (C) 2026 Mahmud Hasan"
LICENSE_NAME = "GNU General Public License v3.0 or later (GPL-3.0-or-later)"
LICENSE_URL = "https://www.gnu.org/licenses/gpl-3.0.html"
LICENSE_NOTICE = (
    "This program is free software: you can redistribute it and/or modify it under the "
    "terms of the GNU General Public License as published by the Free Software Foundation, "
    "either version 3 of the License, or (at your option) any later version.\n\n"
    "Any modified version you distribute must also be released under the GPL, with its "
    "complete source code, so it stays free software.\n\n"
    "This program is distributed in the hope that it will be useful, but WITHOUT ANY "
    "WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A "
    "PARTICULAR PURPOSE. See the GNU General Public License for more details.")
CCI_GIT_URL = "https://github.com/conan-io/conan-center-index.git"
CCI_API = "https://api.github.com/repos/conan-io/conan-center-index"
CACHE_DIR = Path.home() / ".conanwalker"
REQ_KINDS = ("requires", "tool_requires", "build_requires", "test_requires")
USER_AGENT = "ConanWalker/1.0"


# --------------------------------------------------------------------------- #
#  Data model
# --------------------------------------------------------------------------- #
@dataclass
class Requirement:
    name: str
    spec: Optional[str]          # exact version, "[range]", or None (= latest)
    kind: str = "requires"       # requires | tool_requires | test_requires
    raw: str = ""
    parent: str = "(root)"
    via: str = "conanfile"       # conanfile | cmake
    parent_key: str = ""         # node key of the parent ("" = the root recipe)
    candidates: list = field(default_factory=list)   # CMake-derived: possible CCI names
    soft: bool = False           # version is only a hint (fall back to latest)


@dataclass
class Options:
    target: Path
    transitive: bool = True
    cmake_fallback: bool = True         # scan CMakeLists.txt when a recipe lists no deps
    cmake_always: bool = False          # ... or always, in addition to the recipe
    include_tool_requires: bool = True
    include_test_requires: bool = False
    recipe_source: str = "git"          # git | api
    source_mode: str = "git"            # git (clone when possible) | archive | skip
    shallow: bool = True
    overwrite: bool = False
    github_token: str = ""
    write_report: bool = True           # report + PDF tree into the target folder

    def kinds(self) -> set:
        k = {"requires"}
        if self.include_tool_requires:
            k.add("tool_requires")
        if self.include_test_requires:
            k.add("test_requires")
        return k


class Cancelled(Exception):
    pass


# --------------------------------------------------------------------------- #
#  Reference / recipe parsing
# --------------------------------------------------------------------------- #
def split_reference(ref: str) -> tuple[Optional[str], Optional[str]]:
    """'zlib/1.3.1@user/channel#rev' -> ('zlib', '1.3.1'). 'zlib/' -> ('zlib', None)."""
    ref = ref.strip().split("#", 1)[0].split("@", 1)[0].strip()
    if "/" not in ref:
        return None, None
    name, version = ref.split("/", 1)
    name, version = name.strip(), version.strip()
    if not name or not re.match(r"^[A-Za-z0-9_][A-Za-z0-9_.+\-]*$", name):
        return None, None
    return name, (version or None)


def _string_of(node) -> tuple[Optional[str], bool]:
    """Best-effort static evaluation of a string expression.
    Returns (text, complete). If not complete, text is the literal prefix."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value, True
    if isinstance(node, ast.JoinedStr):                       # f"zlib/{ver}"
        prefix = ""
        for v in node.values:
            if isinstance(v, ast.Constant) and isinstance(v.value, str):
                prefix += v.value
            else:
                return prefix, False
        return prefix, True
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):   # "zlib/" + ver
        left, done = _string_of(node.left)
        if left is None or not done:
            return left, False
        right, done2 = _string_of(node.right)
        return (left + right, done2) if right is not None else (left, False)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod):   # "zlib/%s" % ver
        left, _ = _string_of(node.left)
        return (left.split("%", 1)[0], False) if left else (None, False)
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "format"):                   # "zlib/{}".format(ver)
        base, _ = _string_of(node.func.value)
        return (base.split("{", 1)[0], False) if base else (None, False)
    if isinstance(node, (ast.Tuple, ast.List)) and node.elts:  # conan 1: ("zlib/1.2", "private")
        return _string_of(node.elts[0])
    return None, False


def _normalise_kind(kind: str) -> str:
    return "tool_requires" if kind == "build_requires" else kind


def parse_conanfile_py(path: Path) -> tuple[list[Requirement], list[str]]:
    """Statically parse a conanfile.py (never executes it).
    Every requires()/tool_requires()/... call and class attribute is collected,
    including ones inside `if self.options...` blocks (a superset of real deps)."""
    text = Path(path).read_text(encoding="utf-8", errors="replace")
    tree = ast.parse(text, filename=str(path))
    found: list[Requirement] = []
    warnings: list[str] = []

    def add(node, kind):
        s, complete = _string_of(node)
        if s is None:
            warnings.append(f"line {getattr(node, 'lineno', '?')}: {kind}() with a non-literal "
                            f"reference, skipped")
            return
        if not complete:
            # Partially known, e.g. f"openssl/{self._openssl_version}" -> take latest
            if "/" not in s:
                warnings.append(f"line {node.lineno}: cannot work out package name from "
                                f"'{s}...', skipped")
                return
            s = s.split("/", 1)[0] + "/"
        name, version = split_reference(s)
        if not name:
            return
        if not complete:
            warnings.append(f"line {node.lineno}: version of '{name}' is computed at runtime; "
                            f"latest ConanCenter version will be used")
        found.append(Requirement(name, version, _normalise_kind(kind), raw=s))

    def add_value(value, kind):
        if isinstance(value, (ast.List, ast.Tuple)):
            # a list of refs, or a single conan-1 style ("ref", "private") tuple
            if value.elts and all(isinstance(e, (ast.List, ast.Tuple)) for e in value.elts):
                for e in value.elts:
                    add(e, kind)
            elif (len(value.elts) == 2 and isinstance(value.elts[1], ast.Constant)
                  and value.elts[1].value in ("private", "override")):
                add(value.elts[0], kind)
            else:
                for e in value.elts:
                    add(e, kind)
        else:
            add(value, kind)

    for node in ast.walk(tree):
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            for t in targets:
                if isinstance(t, ast.Name) and t.id in REQ_KINDS and node.value is not None:
                    add_value(node.value, t.id)
        elif isinstance(node, ast.Call):
            f = node.func
            if isinstance(f, ast.Attribute) and f.attr in REQ_KINDS and node.args:
                add(node.args[0], f.attr)

    return _dedupe(found), warnings


def parse_conanfile_txt(path: Path) -> tuple[list[Requirement], list[str]]:
    section = None
    found: list[Requirement] = []
    for line in Path(path).read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        m = re.match(r"^\[(\w+)\]$", line)
        if m:
            section = m.group(1)
            continue
        if section in REQ_KINDS:
            name, version = split_reference(line)
            if name:
                found.append(Requirement(name, version, _normalise_kind(section), raw=line))
    return _dedupe(found), []


def parse_recipe(path: Path) -> tuple[list[Requirement], list[str]]:
    path = Path(path)
    if path.suffix.lower() == ".txt":
        return parse_conanfile_txt(path)
    return parse_conanfile_py(path)


# --------------------------------------------------------------------------- #
#  CMake scanning (fallback when a recipe declares no dependencies)
# --------------------------------------------------------------------------- #
# CMake / pkg-config names whose ConanCenter name is not simply the lower-case name
CMAKE_TO_CCI = {k.lower(): v for k, v in {
    "ZLIB": "zlib", "OpenSSL": "openssl", "Boost": "boost", "GTest": "gtest", "GMock": "gtest",
    "CURL": "libcurl", "libcurl": "libcurl", "PNG": "libpng", "libpng16": "libpng",
    "JPEG": "libjpeg", "libjpeg": "libjpeg", "TIFF": "libtiff", "libtiff-4": "libtiff",
    "BZip2": "bzip2", "LibLZMA": "xz_utils", "liblzma": "xz_utils", "LZ4": "lz4", "liblz4": "lz4",
    "ZSTD": "zstd", "libzstd": "zstd", "Protobuf": "protobuf", "gRPC": "grpc", "Eigen3": "eigen",
    "eigen3": "eigen", "SQLite3": "sqlite3", "sqlite3": "sqlite3", "LibXml2": "libxml2",
    "libxml-2.0": "libxml2", "EXPAT": "expat", "Freetype": "freetype", "freetype2": "freetype",
    "GLEW": "glew", "glfw3": "glfw", "SDL2": "sdl", "sdl2": "sdl", "SDL3": "sdl",
    "Iconv": "libiconv", "Intl": "libgettext", "LibArchive": "libarchive", "Snappy": "snappy",
    "Catch2": "catch2", "benchmark": "benchmark", "absl": "abseil", "yaml-cpp": "yaml-cpp",
    "ICU": "icu", "PostgreSQL": "libpq", "libpq": "libpq", "Qt5": "qt", "Qt6": "qt",
    "OpenCV": "opencv", "FFMPEG": "ffmpeg", "libavcodec": "ffmpeg", "libavformat": "ffmpeg",
    "libavutil": "ffmpeg", "libswscale": "ffmpeg", "libswresample": "ffmpeg",
    "libavfilter": "ffmpeg", "libavdevice": "ffmpeg", "GIF": "giflib", "WebP": "libwebp",
    "libwebp": "libwebp", "Brotli": "brotli", "c-ares": "c-ares", "libcares": "c-ares",
    "libuv": "libuv", "Libevent": "libevent", "Flatbuffers": "flatbuffers",
    "FlatBuffers": "flatbuffers", "doctest": "doctest", "CLI11": "cli11", "Microsoft.GSL": "ms-gsl",
    "TBB": "onetbb", "OpenEXR": "openexr", "Imath": "imath", "harfbuzz": "harfbuzz",
    "LibSSH2": "libssh2", "Libssh2": "libssh2", "Ogg": "ogg", "Vorbis": "vorbis", "FLAC": "flac",
    "Opus": "opus", "opus": "opus", "glm": "glm", "assimp": "assimp", "Bullet": "bullet3",
    "pybind11": "pybind11", "xxHash": "xxhash", "libusb-1.0": "libusb", "LibUSB": "libusb",
    "Fontconfig": "fontconfig", "cairo": "cairo", "glib-2.0": "glib", "gio-2.0": "glib",
    "gobject-2.0": "glib", "gmodule-2.0": "glib", "gthread-2.0": "glib", "libssl": "openssl",
    "libcrypto": "openssl", "x264": "libx264", "x265": "libx265", "libdrm": "libdrm",
    "GnuTLS": "gnutls", "Nettle": "nettle", "GMP": "gmp", "MPFR": "mpfr", "LibLZ4": "lz4",
    "Threads::Threads": "", "msgpack": "msgpack-cxx", "msgpack-cxx": "msgpack-cxx",
    "nlohmann_json": "nlohmann_json", "RapidJSON": "rapidjson", "TinyXML2": "tinyxml2",
    "pugixml": "pugixml", "Lua": "lua", "LibXslt": "libxslt", "BISON": "bison", "FLEX": "flex",
    "LibYAML": "libyaml", "yaml-0.1": "libyaml", "Libunwind": "libunwind", "libunwind": "libunwind",
    "CapnProto": "capnproto", "Thrift": "thrift", "ZeroMQ": "zeromq", "libzmq": "zeromq",
    "cppzmq": "cppzmq", "Poco": "poco", "date": "date", "range-v3": "range-v3",
    "magic_enum": "magic_enum", "cxxopts": "cxxopts", "tl-expected": "tl-expected",
    "utf8cpp": "utfcpp", "unofficial-sqlite3": "sqlite3", "Vulkan": "vulkan-loader",
}.items()}

# Toolchain / system / CMake-internal packages that are not ConanCenter dependencies
CMAKE_IGNORE = {x.lower() for x in (
    "Threads", "PkgConfig", "Python", "Python2", "Python3", "PythonInterp", "PythonLibs",
    "Perl", "Git", "Doxygen", "Sphinx", "OpenMP", "CUDA", "CUDAToolkit", "MPI", "OpenGL", "OpenCL",
    "X11", "Java", "JNI", "Matlab", "Ruby", "Subversion", "Hg", "LATEX", "ImageMagick", "GTK2",
    "GTK3", "Wget", "UnixCommands", "Patch", "Backtrace", "ClangFormat", "Coverage", "LCOV",
    "Valgrind", "Gcov", "Cygwin", "MSYS", "Dl", "Rt", "M", "Atomic", "Filesystem", "WindowsSDK",
    "CMakePackageConfigHelpers", "GNUInstallDirs", "Ccache", "Ninja", "PythonExtensions",
)}

SKIP_SCAN_DIRS = {
    "test", "tests", "testing", "unittest", "unittests", "example", "examples", "sample",
    "samples", "demo", "demos", "doc", "docs", "documentation", "third_party", "thirdparty",
    "3rdparty", "third-party", "external", "externals", "extern", "vendor", "vendored", "deps",
    "benchmark", "benchmarks", "bench", "fuzz", "fuzzing", "build", "out", "contrib", "_deps",
    "help", "utilities", "bundled", "submodules", "subprojects",
}
CMAKE_SCAN_MAX_DEPTH = 4
PKG_KEYWORDS = {"REQUIRED", "QUIET", "NO_CMAKE_PATH", "NO_CMAKE_ENVIRONMENT_PATH",
                "IMPORTED_TARGET", "GLOBAL"}
_CMAKE_CMD_RE = re.compile(
    r"\b(find_package|find_dependency|pkg_check_modules|pkg_search_module|"
    r"fetchcontent_declare|cpmaddpackage|cpmfindpackage)\s*\(([^()]*(?:\([^()]*\)[^()]*)*)\)",
    re.I)
_TOKEN_RE = re.compile(r'"[^"]*"|[^\s"]+')


def cci_candidates(name: str, lib_variants: bool = True) -> list[str]:
    """Possible ConanCenter names for a CMake / pkg-config / repo name, best first."""
    low = name.strip().strip('"').lower()
    out: list[str] = []

    def add(x):
        if x and x not in out:
            out.append(x)

    if low in CMAKE_TO_CCI:
        if not CMAKE_TO_CCI[low]:
            return []
        add(CMAKE_TO_CCI[low])
    add(low)
    add(low.replace("_", "-"))
    add(low.replace("-", "_"))
    add(re.sub(r"[-_.]?\d+(\.\d+)*$", "", low))      # glfw3 -> glfw, libfoo-1.0 -> libfoo
    if lib_variants:
        for x in list(out):
            add(x[3:] if x.startswith("lib") else "lib" + x)
    return out


def _strip_cmake_comments(text: str) -> str:
    text = re.sub(r"#\[(=*)\[.*?\]\1\]", "", text, flags=re.S)       # bracket comments
    lines = []
    for line in text.splitlines():
        in_q = False
        for i, ch in enumerate(line):
            if ch == '"':
                in_q = not in_q
            elif ch == "#" and not in_q:
                line = line[:i]
                break
        lines.append(line)
    return "\n".join(lines)


def _version_tag(tag: Optional[str]) -> Optional[str]:
    if not tag:
        return None
    m = re.match(r"^(?:v|release-|version-)?(\d+(?:[._]\d+)+)$", tag.strip(), re.I)
    return m.group(1).replace("_", ".") if m else None


def _repo_names(repo: str) -> tuple:
    """'https://github.com/nlohmann/json.git' -> ('json', 'nlohmann_json', 'nlohmann-json')"""
    parts = [x for x in re.split(r"[/:]", repo.strip().rstrip("/")) if x]
    if not parts:
        return ()
    name = parts[-1].removesuffix(".git")
    if len(parts) < 2:
        return (name,)
    owner = parts[-2]
    return (name, f"{owner}_{name}", f"{owner}-{name}")


def cmake_files(root: Path) -> list[Path]:
    """CMakeLists.txt and *Config.cmake.in files under root, skipping tests,
    examples, docs and vendored third-party folders."""
    root = Path(root)
    found: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        depth = len(Path(dirpath).relative_to(root).parts)
        if depth >= CMAKE_SCAN_MAX_DEPTH:
            dirnames[:] = []
        else:
            dirnames[:] = sorted(d for d in dirnames
                                 if d.lower() not in SKIP_SCAN_DIRS and not d.startswith("."))
        for f in sorted(filenames):
            fl = f.lower()
            if fl == "cmakelists.txt" or fl.endswith("config.cmake.in"):
                found.append(Path(dirpath) / f)
    return found


def scan_cmake(root: Path, exclude: Optional[set] = None) -> tuple[list[Requirement], list[str]]:
    """Collect dependencies from find_package / find_dependency / pkg_check_modules /
    pkg_search_module / FetchContent_Declare / CPMAddPackage in a source tree."""
    root = Path(root)
    exclude = {e.lower() for e in (exclude or set())}
    reqs: list[Requirement] = []
    files = cmake_files(root)

    for path in files:
        try:
            text = _strip_cmake_comments(path.read_text(encoding="utf-8", errors="replace"))
        except OSError:
            continue
        rel = path.relative_to(root).as_posix()

        def add(nm: str, spec: Optional[str], cmd: str, extra=()):
            if not nm or "$" in nm or "@" in nm or nm.lower() in CMAKE_IGNORE:
                return
            cands: list[str] = []
            for lib in (False, True):        # exact/owner_repo names before lib-prefix guesses
                for n in (nm, *extra):
                    for c in cci_candidates(n, lib):
                        if c not in cands:
                            cands.append(c)
            if not cands or nm.lower() in exclude or cands[0] in exclude:
                return
            reqs.append(Requirement(nm, spec, "requires", raw=f"{cmd}({nm}) in {rel}",
                                    via="cmake", candidates=cands, soft=True))

        for m in _CMAKE_CMD_RE.finditer(text):
            cmd = m.group(1).lower()
            toks = [t.strip('"') for t in _TOKEN_RE.findall(m.group(2))]
            if not toks:
                continue
            if cmd in ("find_package", "find_dependency"):
                ver = toks[1] if len(toks) > 1 and re.match(r"^\d+(\.\d+)*$", toks[1]) else None
                add(toks[0], f"[>={ver}]" if ver else None, cmd)
            elif cmd in ("pkg_check_modules", "pkg_search_module"):
                for t in toks[1:]:
                    if t.upper() in PKG_KEYWORDS or re.match(r"^[<>=\d]", t):
                        continue
                    mm = re.match(r"^([A-Za-z0-9_.+\-]+?)(?:(>=|<=|=|>|<)(.+))?$", t)
                    if not mm:
                        continue
                    op, ver = mm.group(2), mm.group(3)
                    spec = f"[{op}{ver}]" if op in (">=", ">") else (ver if op == "=" else None)
                    add(mm.group(1), spec, cmd)
            elif cmd == "fetchcontent_declare":
                kv = {toks[i].upper(): toks[i + 1] for i in range(1, len(toks) - 1)}
                ver = _version_tag(kv.get("GIT_TAG"))
                add(toks[0], ver, "FetchContent_Declare", _repo_names(kv.get("GIT_REPOSITORY", "")))
            else:  # CPMAddPackage / CPMFindPackage
                short = re.match(r"^(?:gh|gl|bb):([^/]+)/([^@#\s]+)(?:@([^#\s]+))?(?:#(\S+))?$", toks[0])
                if short:
                    ver = _version_tag(short.group(3)) or _version_tag(short.group(4)) or short.group(3)
                    add(short.group(2), ver, "CPMAddPackage",
                        _repo_names(f"{short.group(1)}/{short.group(2)}"))
                    continue
                kv = {toks[i].upper(): toks[i + 1] for i in range(len(toks) - 1)}
                nm = kv.get("NAME") or kv.get("GITHUB_REPOSITORY", "").rsplit("/", 1)[-1]
                ver = kv.get("VERSION") or _version_tag(kv.get("GIT_TAG"))
                add(nm, ver, "CPMAddPackage",
                    _repo_names(kv.get("GITHUB_REPOSITORY") or kv.get("GIT_REPOSITORY", "")))

    # one entry per CMake name (case-insensitive), prefer one with a version
    out: dict[str, Requirement] = {}
    for r in reqs:
        k = r.name.lower()
        if k not in out or (out[k].spec is None and r.spec is not None):
            out[k] = r
    notes = [f"scanned {len(files)} CMake file(s) under {root}"]
    return list(out.values()), notes


def parse_root(path: Path, use_cmake: bool = True, cmake_always: bool = False
               ) -> tuple[list[Requirement], list[str]]:
    """Dependencies of the recipe the user opened. Falls back to CMakeLists.txt in
    the same folder (recursively) when the recipe declares none."""
    path = Path(path)
    if path.name.lower() == "cmakelists.txt":
        return scan_cmake(path.parent)
    reqs, warns = parse_recipe(path)
    if use_cmake and (not reqs or cmake_always):
        if (path.parent / "CMakeLists.txt").exists():
            creqs, notes = scan_cmake(path.parent)
            known = {r.name.lower() for r in reqs}
            creqs = [c for c in creqs if not (set(c.candidates[:1]) & known)]
            reason = "no dependencies in " + path.name if not reqs else "also scanning CMake"
            warns.append(f"{reason}: {notes[0]}, found {len(creqs)}")
            reqs = reqs + creqs
        elif not reqs:
            warns.append("no dependencies in the recipe and no CMakeLists.txt next to it")
    return reqs, warns


def _dedupe(reqs: list[Requirement]) -> list[Requirement]:
    """Keep one entry per (name, kind); prefer an explicit version over 'latest'."""
    out: dict[tuple, Requirement] = {}
    for r in reqs:
        key = (r.name, r.kind)
        if key not in out or (out[key].spec is None and r.spec is not None):
            out[key] = r
    return list(out.values())


# --------------------------------------------------------------------------- #
#  Versions and ranges (Conan 2 syntax: [>=1.0 <2], [~1.2], [^1.2], a || b)
# --------------------------------------------------------------------------- #
def version_key(v: str):
    key = []
    for p in re.split(r"[.\-+_]", str(v)):
        key.append((0, int(p), "") if p.isdigit() else (1, 0, p))
    return tuple(key)


def _bump(ver: str, index: int) -> Optional[str]:
    parts = ver.split(".")
    try:
        parts = parts[: index + 1]
        while len(parts) <= index:
            parts.append("0")
        parts[index] = str(int(parts[index]) + 1)
        return ".".join(parts)
    except ValueError:
        return None


def _conditions(group: str) -> list[tuple[str, str]]:
    conds = []
    for tok in group.split():
        m = re.match(r"^(>=|<=|>|<|=|~|\^)?(.+)$", tok)
        if not m:
            continue
        op, ver = m.group(1) or "=", m.group(2)
        if ver == "*":
            continue
        if op == "~":
            conds.append((">=", ver))
            up = _bump(ver, 1 if "." in ver else 0)
            if up:
                conds.append(("<", up))
        elif op == "^":
            conds.append((">=", ver))
            parts = ver.split(".")
            idx = 1 if (parts[0] == "0" and len(parts) > 1) else 0
            up = _bump(ver, idx)
            if up:
                conds.append(("<", up))
        else:
            conds.append((op, ver))
    return conds


def _satisfies(v: str, conds) -> bool:
    kv = version_key(v)
    for op, ref in conds:
        if ref.endswith(".*"):
            if not (v == ref[:-2] or v.startswith(ref[:-1])):
                return False
            continue
        kr = version_key(ref)
        ok = {">=": kv >= kr, "<=": kv <= kr, ">": kv > kr, "<": kv < kr,
              "=": kv == kr}.get(op, False)
        if not ok:
            return False
    return True


def resolve_version(spec: Optional[str], available: list[str]) -> Optional[str]:
    available = [str(a) for a in available]
    if not available:
        return None
    ordered = sorted(available, key=version_key)
    stable = [v for v in ordered if "-" not in v] or ordered
    if not spec:
        return stable[-1]
    spec = spec.strip()
    if spec.startswith("[") and spec.endswith("]"):
        body = spec[1:-1]
        allow_pre = "include_prerelease" in body
        body = body.split(",", 1)[0]
        pool = ordered if allow_pre else stable
        groups = [_conditions(g) for g in body.split("||")]
        matches = [v for v in pool if any(_satisfies(v, g) for g in groups)]
        return matches[-1] if matches else None
    return spec if spec in available else None


# --------------------------------------------------------------------------- #
#  Small helpers: processes, HTTP, files
# --------------------------------------------------------------------------- #
class Runner:
    """Runs subprocesses so that Stop can kill them."""

    def __init__(self, cancel: threading.Event):
        self.cancel = cancel

    def run(self, args: list[str], cwd: Optional[Path] = None, timeout: int = 3600) -> tuple[int, str]:
        kwargs = {}
        if os.name == "nt":
            kwargs["creationflags"] = 0x08000000  # CREATE_NO_WINDOW
        env = dict(os.environ, GIT_TERMINAL_PROMPT="0")
        proc = subprocess.Popen(args, cwd=str(cwd) if cwd else None, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, env=env,
                                text=True, encoding="utf-8", errors="replace", **kwargs)
        start = time.time()
        while True:
            try:
                out, _ = proc.communicate(timeout=0.5)
                return proc.returncode, out or ""
            except subprocess.TimeoutExpired:
                if self.cancel.is_set():
                    proc.kill()
                    proc.communicate()
                    raise Cancelled()
                if time.time() - start > timeout:
                    proc.kill()
                    out, _ = proc.communicate()
                    return -1, (out or "") + "\n(timed out)"


def git_available() -> bool:
    return shutil.which("git") is not None


def http_get(url: str, token: str = "", accept: str = "") -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    if token and "github" in url:
        req.add_header("Authorization", f"Bearer {token}")
    if accept:
        req.add_header("Accept", accept)
    with urllib.request.urlopen(req, timeout=120) as r:
        return r.read()


def download(url: str, dest: Path, cancel: threading.Event,
             progress: Optional[Callable[[int, int], None]] = None) -> None:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=120) as r, open(dest, "wb") as f:
        total = int(r.headers.get("Content-Length") or 0)
        done = 0
        while True:
            if cancel.is_set():
                raise Cancelled()
            chunk = r.read(1 << 16)
            if not chunk:
                break
            f.write(chunk)
            done += len(chunk)
            if progress:
                progress(done, total)


def _on_rm_error(func, path, _exc):
    os.chmod(path, stat.S_IWRITE)     # .git objects are read-only on Windows
    func(path)


def rmtree(path: Path) -> None:
    if path.exists():
        if sys.version_info >= (3, 12):
            shutil.rmtree(path, onexc=_on_rm_error)
        else:
            shutil.rmtree(path, onerror=_on_rm_error)


def is_nonempty_dir(p: Path) -> bool:
    return p.is_dir() and any(p.iterdir())


def load_yaml(path: Path):
    if yaml is None:
        raise RuntimeError("PyYAML is not installed. Run:  pip install pyyaml")
    with open(path, "r", encoding="utf-8") as f:
        return yaml.safe_load(f) or {}


def safe_extract(archive: Path, dest: Path) -> None:
    """Extract tar/zip into dest, refusing paths that escape it, and strip a
    single top-level folder (archives are usually project-1.2.3/...)."""
    tmp = Path(tempfile.mkdtemp(prefix="cw_extract_", dir=dest.parent))
    try:
        root = tmp.resolve()
        name = archive.name.lower()
        if name.endswith(".zip"):
            with zipfile.ZipFile(archive) as z:
                for m in z.namelist():
                    if not (root / m).resolve().is_relative_to(root):
                        raise RuntimeError(f"unsafe path in archive: {m}")
                z.extractall(tmp)
        else:
            with tarfile.open(archive) as t:
                if hasattr(tarfile, "data_filter"):
                    t.extractall(tmp, filter="data")
                else:
                    for m in t.getmembers():
                        if not (root / m.name).resolve().is_relative_to(root):
                            raise RuntimeError(f"unsafe path in archive: {m.name}")
                    t.extractall(tmp)
        entries = list(tmp.iterdir())
        src = entries[0] if len(entries) == 1 and entries[0].is_dir() else tmp
        dest.mkdir(parents=True, exist_ok=True)
        for item in src.iterdir():
            shutil.move(str(item), str(dest / item.name))
    finally:
        rmtree(tmp)


# --------------------------------------------------------------------------- #
#  ConanCenter recipe fetchers
# --------------------------------------------------------------------------- #
class CciGitFetcher:
    """Sparse, blob-less clone of conan-center-index; only recipes/<name> that we
    ask for are checked out. Cached in ~/.conanwalker between runs."""

    def __init__(self, runner: Runner, log: Callable[[str], None]):
        self.runner, self.log = runner, log
        self.path = CACHE_DIR / "conan-center-index"
        self._ready = False
        self._names: Optional[dict] = None

    def available_names(self) -> dict:
        """lower-case name -> ConanCenter recipe name (trees are present in a
        blob-less clone, so this needs no checkout)."""
        if self._names is None:
            self.ensure()
            out = self._git("ls-tree", "--name-only", "HEAD", "recipes/")
            names = [l.strip().split("/", 1)[-1] for l in out.splitlines() if l.strip()]
            self._names = {n.lower(): n for n in names}
        return self._names

    def _git(self, *args, cwd=None):
        code, out = self.runner.run(["git", *args], cwd=cwd or self.path)
        if code != 0:
            raise RuntimeError(f"git {' '.join(args)} failed:\n{out.strip()}")
        return out

    def ensure(self):
        if self._ready:
            return
        if not git_available():
            raise RuntimeError("git was not found on PATH. Install Git or switch the recipe "
                               "source to 'GitHub API'.")
        CACHE_DIR.mkdir(parents=True, exist_ok=True)
        if (self.path / ".git").exists():
            self.log("Updating cached conan-center-index ...")
            try:
                self._git("fetch", "--depth", "1", "origin", "master")
                self._git("reset", "--hard", "FETCH_HEAD")
            except RuntimeError as e:
                self.log(f"  update failed, using cached copy ({e.args[0].splitlines()[0]})")
        else:
            self.log("Cloning conan-center-index (sparse, first run only) ...")
            rmtree(self.path)
            self._git("clone", "--depth", "1", "--filter=blob:none", "--sparse",
                      CCI_GIT_URL, str(self.path), cwd=CACHE_DIR)
        self._ready = True

    def recipe_dir(self, name: str) -> Optional[Path]:
        self.ensure()
        self._git("sparse-checkout", "add", f"recipes/{name}")
        d = self.path / "recipes" / name
        return d if d.is_dir() else None


class CciApiFetcher:
    """Downloads recipes/<name> via the GitHub contents API (60 requests/hour
    without a token, 5000 with one)."""

    def __init__(self, token: str, cancel: threading.Event, log: Callable[[str], None]):
        self.token, self.cancel, self.log = token, cancel, log
        self.root = CACHE_DIR / "api-recipes"
        self._names: Optional[dict] = None

    def available_names(self) -> dict:
        if self._names is None:
            acc = "application/vnd.github+json"
            top = json.loads(http_get(f"{CCI_API}/git/trees/master", self.token, acc))
            sha = next(e["sha"] for e in top["tree"] if e["path"] == "recipes")
            sub = json.loads(http_get(f"{CCI_API}/git/trees/{sha}", self.token, acc))
            self._names = {e["path"].lower(): e["path"] for e in sub["tree"] if e["type"] == "tree"}
        return self._names

    def _list(self, rel: str):
        url = f"{CCI_API}/contents/{urllib.parse.quote(rel)}?ref=master"
        try:
            return json.loads(http_get(url, self.token, "application/vnd.github+json"))
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return None
            if e.code in (403, 429):
                raise RuntimeError("GitHub API rate limit hit. Add a GitHub token or use the "
                                   "'git' recipe source.") from e
            raise

    def recipe_dir(self, name: str) -> Optional[Path]:
        dest = self.root / name
        rmtree(dest)
        if not self._fetch(f"recipes/{name}", dest):
            return None
        return dest

    def _fetch(self, rel: str, dest: Path) -> bool:
        items = self._list(rel)
        if items is None:
            return False
        dest.mkdir(parents=True, exist_ok=True)
        for it in items:
            if self.cancel.is_set():
                raise Cancelled()
            if it["type"] == "dir":
                self._fetch(it["path"], dest / it["name"])
            elif it["type"] == "file" and it.get("download_url"):
                (dest / it["name"]).write_bytes(http_get(it["download_url"], self.token))
        return True


# --------------------------------------------------------------------------- #
#  Upstream source handling
# --------------------------------------------------------------------------- #
ARCHIVE_EXT = r"(?:\.tar\.gz|\.tar\.bz2|\.tar\.xz|\.tgz|\.tar|\.zip)"
GIT_URL_PATTERNS = [
    # github.com/o/r/archive/refs/tags/v1.2.tar.gz | /archive/<sha>.tar.gz
    re.compile(rf"^https?://github\.com/([^/]+)/([^/]+)/archive/(?:refs/(?:tags|heads)/)?(.+?){ARCHIVE_EXT}$"),
    # github.com/o/r/releases/download/<tag>/file
    re.compile(r"^https?://github\.com/([^/]+)/([^/]+)/releases/download/([^/]+)/"),
    # codeload.github.com/o/r/tar.gz/<ref>
    re.compile(r"^https?://codeload\.github\.com/([^/]+)/([^/]+)/(?:tar\.gz|zip)/(?:refs/tags/)?(.+)$"),
]
GITLAB_PATTERN = re.compile(r"^https?://(gitlab\.[^/]+|gitlab\.com)/(.+?)/-/archive/([^/]+)/")


def git_info_from_url(url: str) -> Optional[tuple[str, str]]:
    """Map a source-archive URL to (git clone url, ref)."""
    for pat in GIT_URL_PATTERNS:
        m = pat.match(url)
        if m:
            owner, repo, ref = m.group(1), m.group(2), urllib.parse.unquote(m.group(3))
            return f"https://github.com/{owner}/{repo}.git", ref
    m = GITLAB_PATTERN.match(url)
    if m:
        return f"https://{m.group(1)}/{m.group(2)}.git", urllib.parse.unquote(m.group(3))
    return None


def source_entries(conandata: dict, version: str) -> list[dict]:
    """Return the list of {url, sha256} dicts for a version (handles str/list urls,
    lists of archives and per-platform nesting)."""
    sources = (conandata or {}).get("sources") or {}
    entry = None
    for k, v in sources.items():
        if str(k) == version:
            entry = v
            break
    if entry is None:
        return []

    def walk(node) -> list[dict]:
        if isinstance(node, dict):
            if "url" in node:
                return [node]
            for v in node.values():           # per-platform: take the first one
                found = walk(v)
                if found:
                    return found
            return []
        if isinstance(node, list):
            out = []
            for v in node:
                out.extend(walk(v))
            return out
        return []

    return walk(entry)


def fetch_source(entries: list[dict], repo_dir: Path, opts: Options, runner: Runner,
                 cancel: threading.Event, log: Callable[[str], None],
                 notes: Optional[list] = None) -> str:
    """Fetch the upstream source. `notes` collects reasons a git repo was not used."""
    notes = notes if notes is not None else []
    if not entries:
        raise RuntimeError("no source URL in conandata.yml for this version")
    if len(entries) > 1:
        log(f"  conandata lists {len(entries)} source archives; using the first")
    entry = entries[0]
    urls = entry["url"] if isinstance(entry["url"], list) else [entry["url"]]
    sha = entry.get("sha256")

    if opts.source_mode == "git" and not git_available():
        notes.append("git not installed")
    if opts.source_mode == "git" and git_available():
        if not any(git_info_from_url(u) for u in urls):
            notes.append("no git repository found for source URL " + urls[0])
        for url in urls:
            info = git_info_from_url(url)
            if not info:
                continue
            clone_url, ref = info
            log(f"  git checkout {clone_url} @ {ref}")
            try:
                git_checkout(clone_url, ref, repo_dir, opts.shallow, runner)
                return f"git: {clone_url} @ {ref}"
            except RuntimeError as e:
                reason = (str(e).strip().splitlines() or ["git error"])[-1][:200]
                notes.append(f"git checkout of {clone_url} @ {ref} failed: {reason}")
                log(f"  git failed ({reason}); falling back to archive")
                rmtree(repo_dir)

    last_err = None
    for url in urls:
        try:
            log(f"  downloading {url}")
            tmpdir = Path(tempfile.mkdtemp(prefix="cw_dl_"))
            try:
                fname = urllib.parse.urlparse(url).path.rsplit("/", 1)[-1] or "source.tar.gz"
                archive = tmpdir / fname
                download(url, archive, cancel)
                if sha:
                    h = hashlib.sha256(archive.read_bytes()).hexdigest()
                    if h.lower() != str(sha).lower():
                        raise RuntimeError(f"sha256 mismatch (expected {sha}, got {h})")
                rmtree(repo_dir)
                if re.search(ARCHIVE_EXT + "$", fname.lower()):
                    safe_extract(archive, repo_dir)
                else:                                  # single file (e.g. a header)
                    repo_dir.mkdir(parents=True, exist_ok=True)
                    shutil.move(str(archive), str(repo_dir / fname))
                return f"archive: {url}"
            finally:
                rmtree(tmpdir)
        except Cancelled:
            raise
        except Exception as e:  # try the next mirror
            last_err = e
            log(f"  failed: {e}")
    raise RuntimeError(f"could not fetch source: {last_err}")


def git_checkout(clone_url: str, ref: str, dest: Path, shallow: bool, runner: Runner) -> None:
    rmtree(dest)
    dest.mkdir(parents=True, exist_ok=True)

    def git(*args):
        code, out = runner.run(["git", *args], cwd=dest)
        if code != 0:
            raise RuntimeError(out.strip() or f"git {args[0]} failed")

    git("init", "-q")
    git("remote", "add", "origin", clone_url)
    if shallow:
        # works for tags, branches and commit SHAs on GitHub/GitLab
        git("fetch", "--depth", "1", "origin", ref)
    else:
        git("fetch", "--tags", "origin")
        try:
            git("rev-parse", "--verify", f"{ref}^{{commit}}")
        except RuntimeError:
            git("fetch", "origin", ref)
            ref = "FETCH_HEAD"
        else:
            git("checkout", "-q", ref)
            return
    git("checkout", "-q", "FETCH_HEAD")


# --------------------------------------------------------------------------- #
#  The walker
# --------------------------------------------------------------------------- #
# Result categories recorded for every package / CMake name
ST_OK = "ok"                         # recipe + git repo
ST_OK_ARCHIVE = "ok_archive"         # recipe + archive, by choice (source = archive)
ST_OK_NOSRC = "ok_nosource"          # recipe ok, source skipped or kept from earlier run
ST_NO_GIT = "no_git"                 # recipe ok, no git repo -> archive downloaded instead
ST_SOURCE_FAILED = "source_failed"   # recipe ok, source could not be fetched
ST_MISSING = "missing"               # package not on ConanCenter
ST_VERSION_MISSING = "version_missing"  # package exists, requested version doesn't
ST_CMAKE_UNMAPPED = "cmake_unmapped"    # CMake name with no ConanCenter package
ST_ERROR = "error"                   # recipe fetch error
ST_PENDING = "pending"               # not processed (run stopped)
ST_EXISTS = "exists"                 # already in the target folder, not downloaded again

STATUS_INFO = {   # key: (short label, long description, severity)
    ST_OK: ("OK", "recipe + git repository", "ok"),
    ST_OK_ARCHIVE: ("OK (archive)", "recipe + source archive", "ok"),
    ST_OK_NOSRC: ("OK", "recipe downloaded (source skipped)", "ok"),
    ST_EXISTS: ("ALREADY EXISTS", "already in the target folder; not downloaded again", "ok"),
    ST_NO_GIT: ("NO GIT REPO", "no git repository; source archive downloaded instead", "warn"),
    ST_SOURCE_FAILED: ("SOURCE FAILED", "recipe downloaded but source could not be fetched", "warn"),
    ST_MISSING: ("MISSING", "package not found on ConanCenter", "missing"),
    ST_VERSION_MISSING: ("VERSION MISSING", "requested version not on ConanCenter", "missing"),
    ST_CMAKE_UNMAPPED: ("MISSING (CMake)", "CMake dependency with no ConanCenter package", "missing"),
    ST_ERROR: ("ERROR", "recipe could not be fetched", "error"),
    ST_PENDING: ("NOT PROCESSED", "run stopped before this package", "pending"),
}
ROOT_KEY = ""


class Walker:
    """Processes dependencies breadth-first and records the result of every
    package and every parent -> child edge (used for the report and PDF tree).
    Callbacks: log(str), status(name, dict), progress(done, total)."""

    def __init__(self, opts: Options, log, status, progress, cancel: threading.Event):
        self.opts, self._ext_log, self.status, self.progress, self.cancel = opts, log, status, progress, cancel
        self.log_lines: list[str] = []
        self.runner = Runner(cancel)
        if opts.recipe_source == "api":
            self.fetcher = CciApiFetcher(opts.github_token, cancel, self.log)
        else:
            self.fetcher = CciGitFetcher(self.runner, self.log)
        self.summary = {"ok": 0, "warn": 0, "error": 0, "skipped": 0}
        self.nodes: dict[str, dict] = {}
        self.edges: list[list] = []
        self._edge_set: set = set()
        self.started = time.time()
        self.finished: Optional[float] = None
        self.outcome = "running"

    # ---- recording -----------------------------------------------------
    def log(self, msg: str):
        self.log_lines.append(msg)
        self._ext_log(msg)

    def _node(self, key: str, req: Optional[Requirement] = None) -> dict:
        n = self.nodes.get(key)
        if n is None:
            n = self.nodes[key] = {
                "name": key, "requested": None, "resolved": None, "kind": None, "via": None,
                "found_in": None, "cci_name": None, "status": ST_PENDING, "source": None,
                "source_detail": None, "folder": None, "problems": [], "notes": [],
                "required_by": []}
        if req is not None and n["kind"] is None:
            n.update(requested=req.spec, kind=req.kind, via=req.via, found_in=req.raw or None)
        return n

    def _edge(self, parent_key: str, child_key: str, kind: str, parent_label: str):
        e = (parent_key, child_key)
        if e in self._edge_set:
            return
        self._edge_set.add(e)
        self.edges.append([parent_key, child_key, kind])
        rb = self.nodes[child_key]["required_by"]
        if parent_label not in rb:
            rb.append(parent_label)

    def _map_cmake(self, req: Requirement) -> Optional[str]:
        names = self.fetcher.available_names()
        for c in req.candidates:
            if c.lower() in names:
                return names[c.lower()]
        return None

    # ---- main loop -----------------------------------------------------
    def run(self, roots: list[Requirement]) -> dict:
        try:
            result = self._run(roots)
            self.outcome = "completed"
            return result
        except Cancelled:
            self.outcome = "stopped by user"
            raise
        except Exception as e:
            self.outcome = f"failed: {e}"
            raise
        finally:
            self.finished = time.time()

    def _run(self, roots: list[Requirement]) -> dict:
        if yaml is None:
            raise RuntimeError("PyYAML is not installed. Run:  pip install pyyaml")
        self.opts.target.mkdir(parents=True, exist_ok=True)
        kinds = self.opts.kinds()
        pending = [r for r in roots if r.kind in kinds]
        for r in pending:                       # show every root in the tree even if stopped early
            key = r.name if not r.candidates else f"{r.name} (CMake)"
            self._node(key, r)["name"] = r.name
        seen: dict[str, Requirement] = {}
        done = 0
        while pending:
            if self.cancel.is_set():
                raise Cancelled()
            req = pending.pop(0)
            if req.candidates:                       # came from CMake: map to a CCI name
                tmp_key = f"{req.name} (CMake)"
                try:
                    real = self._map_cmake(req)
                except Cancelled:
                    raise
                except Exception as e:
                    raise RuntimeError(f"could not list ConanCenter recipes: {e}") from e
                if not real:
                    n = self._node(tmp_key, req)
                    n["name"] = req.name
                    n["status"] = ST_CMAKE_UNMAPPED
                    n["problems"].append(f"no ConanCenter package matches CMake name '{req.name}' "
                                         f"(tried: {', '.join(req.candidates[:6])})")
                    self._edge(req.parent_key, tmp_key, req.kind, req.parent)
                    self.log(f"skip: '{req.name}' ({req.raw}, needed by {req.parent}) has no "
                             f"ConanCenter package")
                    self.summary["skipped"] += 1
                    self.status(req.name, {"state": "MISSING: no ConanCenter package (CMake name)",
                                           "via": "cmake"})
                    continue
                self.nodes.pop(tmp_key, None)       # placeholder from the roots pre-pass
                if real != req.name:
                    self.status(req.name, {"_rename": real})
                n = self._node(real, req)
                n["cci_name"] = real
                n["found_in"] = n["found_in"] or req.raw
                req.name = real
                req.candidates = []
            node = self._node(req.name, req)
            self._edge(req.parent_key, req.name, req.kind, req.parent)
            if req.name in seen:
                prev = seen[req.name]
                if (req.spec or "") != (prev.spec or ""):
                    msg = (f"also wanted as '{req.spec or 'latest'}' by {req.parent}; kept "
                           f"'{prev.spec or 'latest'}' from {prev.parent}")
                    node["notes"].append(msg)
                    self.log(f"note: {req.name} {msg}")
                continue
            seen[req.name] = req
            self.progress(done, done + len(pending) + 1)
            children = self._process(req, node)
            done += 1
            for c in children:
                if c.kind in kinds:
                    pending.append(c)            # duplicates are filtered when popped (edges kept)
                    if c.name not in seen:
                        self.status(c.name, {"spec": c.spec or "latest", "kind": c.kind,
                                             "parent": c.parent, "via": c.via, "state": "queued"})
        self.progress(done, done)
        return self.summary

    def _process(self, req: Requirement, node: dict) -> list[Requirement]:
        name = req.name
        self.log(f"\n=== {name} ({req.spec or 'latest'}) [{req.kind}] from {req.parent}")
        self.status(name, {"spec": req.spec or "latest", "kind": req.kind, "parent": req.parent,
                           "via": req.via, "state": "fetching recipe"})
        dep_dir = self.opts.target / name
        recipe_out, repo_out = dep_dir / "recipe", dep_dir / "repo"
        info = {"name": name, "requested": req.spec, "kind": req.kind, "required_by": req.parent,
                "found_via": req.via if req.via != "cmake" else f"cmake: {req.raw}"}

        # 0. already downloaded by an earlier run? (dependency.json + recipe/ present)
        existing = None
        if not self.opts.overwrite and is_nonempty_dir(recipe_out):
            try:
                existing = json.loads((dep_dir / "dependency.json").read_text(encoding="utf-8"))
                if not existing.get("resolved"):
                    existing = None
            except (OSError, ValueError):
                existing = None
        if existing:
            resolved = existing["resolved"]
            if req.spec and not req.soft and resolve_version(req.spec, [resolved]) is None:
                msg = (f"existing {name}/{resolved} does not satisfy '{req.spec}'; kept it "
                       f"(tick Overwrite to replace)")
                node["notes"].append(msg)
                self.log("  note: " + msg)
            node.update(resolved=resolved, folder=str(dep_dir))
            info = {**existing, **{k: v for k, v in info.items() if k not in ("required_by",)}}
            info["resolved"] = resolved
            have_repo = is_nonempty_dir(repo_out)
            if have_repo or self.opts.source_mode == "skip":
                prev_src = existing.get("source", "")
                kind, _, detail = prev_src.partition(": ")
                if not kind:
                    kind = "git" if (repo_out / ".git").exists() else ("archive" if have_repo else "none")
                node.update(status=ST_EXISTS, source=kind, source_detail=detail or (str(repo_out) if have_repo else None))
                self.log(f"  already in target folder ({name}/{resolved}, source: {kind}); not downloaded again")
                self.status(name, {"resolved": resolved, "recipe": "exists",
                                   "repo": "exists" if have_repo else "skipped"})
                children = self._children(req, node, name, resolved, recipe_out, repo_out)
                self.summary["ok"] += 1
                self.status(name, {"state": "already exists"})
                return children
            self.log(f"  recipe {name}/{resolved} already in target folder; fetching source only")
            node["notes"].append("recipe already existed; source downloaded now")
            self.status(name, {"resolved": resolved, "recipe": "exists", "state": "fetching source"})

        # 1. recipe from ConanCenter (skipped when it is already in the target folder)
        if not existing:
            try:
                cci = self.fetcher.recipe_dir(name)
            except Cancelled:
                raise
            except Exception as e:
                return self._fail(node, ST_ERROR, f"recipe fetch failed: {e}")
            if cci is None or not (cci / "config.yml").exists():
                return self._fail(node, ST_MISSING, "not found on ConanCenter")
            resolved = self._fetch_recipe(req, node, name, cci, dep_dir, recipe_out, info)
            if resolved is None:
                return []
        info["resolved"] = resolved
        return self._source_and_children(req, node, name, resolved, dep_dir, recipe_out, repo_out, info)

    def _fetch_recipe(self, req, node, name, cci, dep_dir, recipe_out, info):
        """Copy the right ConanCenter recipe folder; returns resolved version or None."""
        versions = (load_yaml(cci / "config.yml").get("versions") or {})
        versions = {str(k): v for k, v in versions.items()}
        resolved = resolve_version(req.spec, list(versions))
        if not resolved and req.soft:
            resolved = resolve_version(None, list(versions))
            msg = f"CMake asked for '{req.spec}', not on ConanCenter; used latest {resolved}"
            node["notes"].append(msg)
            self.log("  " + msg)
        if not resolved:
            avail = ", ".join(sorted(versions, key=version_key)[-8:])
            self._fail(node, ST_VERSION_MISSING,
                       f"version '{req.spec}' not on ConanCenter (available: {avail})")
            return None
        folder = (versions[resolved] or {}).get("folder", "all")
        src_folder = cci / folder
        if not src_folder.is_dir():
            self._fail(node, ST_ERROR, f"recipe folder '{folder}' missing in ConanCenter")
            return None

        dep_dir.mkdir(parents=True, exist_ok=True)
        node.update(resolved=resolved, folder=str(dep_dir))
        if self.opts.overwrite or not is_nonempty_dir(recipe_out):
            rmtree(recipe_out)
            shutil.copytree(src_folder, recipe_out)
            shutil.copy2(cci / "config.yml", recipe_out / "config.yml")
            self.log(f"  recipe {name}/{resolved} -> {recipe_out}  (cci folder '{folder}')")
        else:
            self.log("  recipe exists, kept (tick Overwrite to refresh)")
        info.update(resolved=resolved, cci_folder=folder)
        self.status(name, {"resolved": resolved, "recipe": "ok", "state": "fetching source"})
        return resolved

    def _source_and_children(self, req, node, name, resolved, dep_dir, recipe_out, repo_out, info):
        # 2. upstream source
        if self.opts.source_mode == "skip":
            node.update(status=ST_OK_NOSRC, source="skipped")
            self.status(name, {"repo": "skipped"})
        elif is_nonempty_dir(repo_out) and not self.opts.overwrite:
            kept = "git" if (repo_out / ".git").exists() else "archive"
            node.update(status=ST_EXISTS, source=kept, source_detail=str(repo_out))
            node["notes"].append("source already existed in the target folder")
            self.log("  repo already in target folder; not downloaded again")
            self.status(name, {"repo": "exists"})
        else:
            conandata_path = recipe_out / "conandata.yml"
            notes: list[str] = []
            try:
                if not conandata_path.exists():
                    raise RuntimeError("recipe has no conandata.yml (no upstream source listed)")
                entries = source_entries(load_yaml(conandata_path), resolved)
                how = fetch_source(entries, repo_out, self.opts, self.runner, self.cancel,
                                   self.log, notes)
                info["source"] = how
                kind, _, detail = how.partition(": ")
                node.update(source=kind, source_detail=detail)
                if kind == "git":
                    node["status"] = ST_OK
                elif self.opts.source_mode == "git":
                    node["status"] = ST_NO_GIT
                    node["problems"].extend(notes or ["no git repository; archive downloaded"])
                else:
                    node["status"] = ST_OK_ARCHIVE
                self.status(name, {"repo": kind})
            except Cancelled:
                raise
            except Exception as e:
                node.update(status=ST_SOURCE_FAILED, source="failed")
                node["problems"].extend(notes + [f"source: {e}"])
                info["source_error"] = str(e)
                self.log(f"  WARNING: source: {e}")
                self.status(name, {"repo": "failed"})

        if node.get("source") and node["source"] not in ("skipped", "failed") and "source" not in info:
            info["source"] = f"{node['source']}: {node.get('source_detail') or ''}".rstrip(": ")
        (dep_dir / "dependency.json").write_text(json.dumps(info, indent=2), encoding="utf-8")

        children = self._children(req, node, name, resolved, recipe_out, repo_out)
        sev = STATUS_INFO[node["status"]][2]
        self.summary["ok" if sev == "ok" else "warn"] += 1
        self.status(name, {"state": STATUS_INFO[node["status"]][0].lower()
                           if sev == "ok" else STATUS_INFO[node["status"]][0]})
        return children

    def _children(self, req, node, name, resolved, recipe_out, repo_out) -> list[Requirement]:
        # 3. its own dependencies: from the recipe, else from the source's CMake files
        children: list[Requirement] = []
        if self.opts.transitive:
            kids: list[Requirement] = []
            if (recipe_out / "conanfile.py").exists():
                try:
                    kids, warns = parse_conanfile_py(recipe_out / "conanfile.py")
                    for w in warns:
                        self.log(f"  ({name}) {w}")
                except SyntaxError as e:
                    self.log(f"  could not parse recipe for dependencies: {e}")
            wanted = [k for k in kids if k.kind in self.opts.kinds()]
            # CMake fallback only for libraries: a tool's (cmake, ninja, msys2...) own
            # build dependencies are not dependencies of your project
            if (self.opts.cmake_fallback and req.kind == "requires"
                    and (not wanted or self.opts.cmake_always)):
                if is_nonempty_dir(repo_out):
                    ck, cnotes = scan_cmake(repo_out, exclude={name})
                    known = {k.name.lower() for k in kids}
                    ck = [c for c in ck if not (set(c.candidates[:1]) & known)]
                    why = "recipe lists no dependencies" if not wanted else "also scanning CMake"
                    self.log(f"  {why}; {cnotes[0]}"
                             + (f" -> {', '.join(c.name for c in ck)}" if ck else " -> none"))
                    kids += ck
                elif not wanted:
                    self.log("  recipe lists no dependencies and there is no source to scan")
            for k in kids:
                k.parent = f"{name}/{resolved}"
                k.parent_key = name
            children = kids
            rec = [k.name for k in kids if k.via != "cmake"]
            if rec:
                self.log(f"  depends on: {', '.join(rec)}")
        return children

    def _fail(self, node: dict, status: str, msg: str) -> list:
        node["status"] = status
        node["problems"].append(msg)
        level = STATUS_INFO[status][2]
        self.log(f"  {'ERROR' if level == 'error' else 'MISSING' if level == 'missing' else 'WARNING'}: {msg}")
        self.summary["error" if level == "error" else "warn"] += 1
        self.status(node["name"], {"state": f"{STATUS_INFO[status][0]}: {msg}"})
        return []

    # ---- report ----------------------------------------------------------
    def report(self, recipe: Path) -> dict:
        counts: dict[str, int] = {}
        for n in self.nodes.values():
            counts[n["status"]] = counts.get(n["status"], 0) + 1
        o = self.opts
        return {
            "tool": APP_NAME,
            "generated": time.strftime("%Y-%m-%d %H:%M:%S"),
            "started": time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(self.started)),
            "duration_s": round((self.finished or time.time()) - self.started, 1),
            "outcome": self.outcome,
            "recipe": str(Path(recipe).resolve()),
            "root_label": Path(recipe).name,
            "target": str(Path(o.target).resolve()),
            "options": {"transitive": o.transitive, "cmake_fallback": o.cmake_fallback,
                        "cmake_always": o.cmake_always, "tool_requires": o.include_tool_requires,
                        "test_requires": o.include_test_requires, "recipes_from": o.recipe_source,
                        "source": o.source_mode, "shallow": o.shallow, "overwrite": o.overwrite},
            "counts": counts,
            "nodes": self.nodes,
            "edges": self.edges,
            "log": self.log_lines,
        }


# --------------------------------------------------------------------------- #
#  Reports: text, JSON and an A4 PDF dependency tree
# --------------------------------------------------------------------------- #
def tree_rows(report: dict):
    """Depth-first walk of the dependency graph from the root.
    Yields dicts: key, depth, lasts (is-last flag per level), kind, repeat, cycle.
    A package is expanded the first time it appears; later appearances are marked
    'repeat' so shared dependencies don't blow up the tree."""
    children: dict[str, list] = {}
    for p, c, k in report["edges"]:
        children.setdefault(p, []).append((c, k))
    nodes = report["nodes"]
    order = {ST_MISSING: 0, ST_CMAKE_UNMAPPED: 0, ST_VERSION_MISSING: 0}
    for k in children:          # stable, readable order: libraries first, then tools, by name
        children[k].sort(key=lambda ck: (ck[1] != "requires", ck[0].lower()))
    expanded: set = set()

    def walk(key, depth, lasts, path):
        kids = children.get(key, [])
        for i, (c, kind) in enumerate(kids):
            last = i == len(kids) - 1
            cycle = c in path
            repeat = (c in expanded) and not cycle and bool(children.get(c))
            yield {"key": c, "depth": depth, "lasts": lasts + [last], "kind": kind,
                   "repeat": repeat, "cycle": cycle, "node": nodes.get(c, {})}
            if not cycle and not repeat:
                expanded.add(c)
                yield from walk(c, depth + 1, lasts + [last], path | {c})

    yield from walk(ROOT_KEY, 0, [], {ROOT_KEY})
    _ = order


def _node_label(n: dict) -> str:
    v = n.get("resolved") or n.get("requested")
    return f"{n['name']}/{v}" if v and n.get("resolved") else n["name"]


def _ascii_tree(report: dict) -> list[str]:
    lines = [report["root_label"]]
    for r in tree_rows(report):
        n = r["node"]
        prefix = "".join("    " if l else "|   " for l in r["lasts"][:-1])
        prefix += "`-- " if r["lasts"][-1] else "|-- "
        tag = STATUS_INFO.get(n.get("status"), ("?",))[0]
        extra = []
        if r["kind"] != "requires":
            extra.append(r["kind"])
        if not n.get("resolved") and n.get("requested"):
            extra.append(f"wanted {n['requested']}")
        if n.get("via") == "cmake":
            extra.append("via CMake")
        suffix = " (see above)" if r["repeat"] else " (cycle)" if r["cycle"] else ""
        mark = "" if STATUS_INFO.get(n.get("status"), ("", "", "ok"))[2] == "ok" else f"  <-- {tag}"
        if STATUS_INFO.get(n.get("status"), ("", "", "ok"))[2] == "ok":
            mark = ""
        lines.append(f"{prefix}{_node_label(n)}"
                     + (f" [{', '.join(extra)}]" if extra else "") + suffix + mark)
    return lines


def report_sections(report: dict) -> list[tuple[str, str, list[dict]]]:
    """(title, explanation, nodes) groups used by the text report and the PDF."""
    nodes = list(report["nodes"].values())
    by = lambda *st: sorted((n for n in nodes if n["status"] in st), key=lambda n: n["name"].lower())
    return [
        ("Missing packages (not on ConanCenter)", STATUS_INFO[ST_MISSING][1], by(ST_MISSING)),
        ("Missing versions", STATUS_INFO[ST_VERSION_MISSING][1], by(ST_VERSION_MISSING)),
        ("CMake dependencies with no ConanCenter package", STATUS_INFO[ST_CMAKE_UNMAPPED][1],
         by(ST_CMAKE_UNMAPPED)),
        ("Missing git repositories (archive downloaded instead)", STATUS_INFO[ST_NO_GIT][1],
         by(ST_NO_GIT)),
        ("Source download failures", STATUS_INFO[ST_SOURCE_FAILED][1], by(ST_SOURCE_FAILED)),
        ("Errors", STATUS_INFO[ST_ERROR][1], by(ST_ERROR)),
        ("Not processed", STATUS_INFO[ST_PENDING][1], by(ST_PENDING)),
        ("Successful downloads", "recipe and source fetched", by(ST_OK, ST_OK_ARCHIVE, ST_OK_NOSRC)),
        ("Already present (not downloaded again)", STATUS_INFO[ST_EXISTS][1], by(ST_EXISTS)),
    ]


def write_text_report(report: dict, path: Path) -> None:
    c = report["counts"]
    L = [f"{APP_NAME} report", "=" * 72,
         f"Generated : {report['generated']}   (run took {report['duration_s']} s, {report['outcome']})",
         f"Recipe    : {report['recipe']}",
         f"Target    : {report['target']}",
         "Options   : " + ", ".join(f"{k}={v}" for k, v in report["options"].items()),
         "", "SUMMARY", "-" * 72]
    total = sum(c.values())
    L.append(f"  Total entries                : {total}")
    for st, (label, desc, _) in STATUS_INFO.items():
        if c.get(st):
            L.append(f"  {label:<16} {c[st]:>4}   {desc}")
    for title, _desc, group in report_sections(report):
        L += ["", f"{title.upper()} ({len(group)})", "-" * 72]
        if not group:
            L.append("  (none)")
            continue
        for n in group:
            L.append(f"  {_node_label(n):<40} {n.get('kind') or '':<14} "
                     f"required by: {', '.join(n['required_by']) or '-'}")
            if n.get("requested") and n["requested"] != n.get("resolved"):
                L.append(f"      requested : {n['requested']}")
            if n.get("found_in") and n.get("via") == "cmake":
                L.append(f"      found in  : {n['found_in']}")
            if n.get("source") and n["status"] in (ST_OK, ST_OK_ARCHIVE, ST_OK_NOSRC, ST_NO_GIT, ST_EXISTS):
                L.append(f"      source    : {n['source']}"
                         + (f"  {n['source_detail']}" if n.get("source_detail") else ""))
            for p in n["problems"]:
                L.append(f"      problem   : {p}")
            for note in n["notes"]:
                L.append(f"      note      : {note}")
    L += ["", "DEPENDENCY TREE", "-" * 72, *_ascii_tree(report),
          "", "FULL LOG", "-" * 72, *report["log"]]
    Path(path).write_text("\n".join(L) + "\n", encoding="utf-8")


def write_pdf_tree(report: dict, path: Path) -> None:
    """Printable A4 dependency tree with a status marker per package; missing
    packages are drawn in red with a crossed box so they show on B/W prints."""
    from reportlab.lib.pagesizes import A4
    from reportlab.lib import colors
    from reportlab.pdfgen import canvas as rl_canvas
    from reportlab.pdfbase.pdfmetrics import stringWidth

    W, H = A4
    M = 36                      # margins (0.5 inch)
    ROW = 13.5
    INDENT = 13
    SEV_COLOR = {"ok": colors.HexColor("#2E7D32"), "warn": colors.HexColor("#E08600"),
                 "missing": colors.HexColor("#C62828"), "error": colors.HexColor("#6A1B9A"),
                 "pending": colors.HexColor("#757575")}
    GREY = colors.HexColor("#777777")
    LINE = colors.HexColor("#9E9E9E")

    class NumberedCanvas(rl_canvas.Canvas):
        def __init__(self, *a, **k):
            super().__init__(*a, **k)
            self._saved = []

        def showPage(self):
            self._saved.append(dict(self.__dict__))
            self._startPage()

        def save(self):
            total = len(self._saved)
            for state in self._saved:
                self.__dict__.update(state)
                self.setFont("Helvetica", 7.5)
                self.setFillColor(GREY)
                self.drawString(M, M / 2, f"{APP_NAME} - {report['root_label']} - {report['generated']}")
                self.drawRightString(W - M, M / 2, f"Page {self._pageNumber} of {total}")
                super().showPage()
            super().save()

    c = NumberedCanvas(str(path), pagesize=A4)
    c.setTitle(f"Dependency tree - {report['root_label']}")
    c.setAuthor(APP_NAME)
    y = H - M

    def fit(text, font, size, width):
        if stringWidth(text, font, size) <= width:
            return text
        while text and stringWidth(text + "...", font, size) > width:
            text = text[:-1]
        return text + "..."

    def marker(x, yc, sev, r=3.4):
        col = SEV_COLOR[sev]
        c.setStrokeColor(col)
        c.setFillColor(col)
        c.setLineWidth(0.9)
        if sev == "ok":                                       # filled circle
            c.circle(x, yc, r, stroke=0, fill=1)
        elif sev == "warn":                                   # filled triangle
            p = c.beginPath()
            p.moveTo(x - r, yc - r * 0.85)
            p.lineTo(x + r, yc - r * 0.85)
            p.lineTo(x, yc + r)
            p.close()
            c.drawPath(p, stroke=0, fill=1)
        elif sev in ("missing", "error"):                     # crossed box
            c.setFillColor(colors.white)
            c.rect(x - r, yc - r, 2 * r, 2 * r, stroke=1, fill=1)
            c.line(x - r, yc - r, x + r, yc + r)
            c.line(x - r, yc + r, x + r, yc - r)
        else:                                                 # hollow circle
            c.circle(x, yc, r, stroke=1, fill=0)

    def new_page(continued=True):
        nonlocal y
        c.showPage()
        y = H - M
        if continued:
            c.setFont("Helvetica-Oblique", 8)
            c.setFillColor(GREY)
            c.drawString(M, y - 8, f"Dependency tree - {report['root_label']} (continued)")
            y -= 22

    def need(h):
        if y - h < M + 14:
            new_page()

    # ---- header -----------------------------------------------------------
    c.setFont("Helvetica-Bold", 16)
    c.setFillColor(colors.black)
    c.drawString(M, y - 16, fit(f"Dependency tree: {report['root_label']}", "Helvetica-Bold", 16, W - 2 * M))
    y -= 30
    c.setFont("Helvetica", 8.5)
    for label, val in (("Recipe", report["recipe"]), ("Target", report["target"]),
                       ("Generated", f"{report['generated']}  ({report['outcome']})")):
        c.setFillColor(GREY)
        c.drawString(M, y, label)
        c.setFillColor(colors.black)
        c.drawString(M + 52, y, fit(val, "Helvetica", 8.5, W - 2 * M - 52))
        y -= 11.5

    # summary boxes
    y -= 6
    counts = report["counts"]
    groups = [("OK", ("ok",)), ("No git repo / source failed", ("warn",)),
              ("Missing", ("missing",)), ("Errors", ("error",)), ("Not processed", ("pending",))]
    bx = M
    bw = (W - 2 * M - 4 * 6) / 5
    for label, sevs in groups:
        num = sum(v for k, v in counts.items() if STATUS_INFO[k][2] in sevs)
        col = SEV_COLOR[sevs[0]]
        c.setStrokeColor(col)
        c.setLineWidth(1)
        c.roundRect(bx, y - 30, bw, 30, 3, stroke=1, fill=0)
        c.setFillColor(col)
        c.setFont("Helvetica-Bold", 13)
        c.drawString(bx + 7, y - 15, str(num))
        c.setFont("Helvetica", 7)
        c.setFillColor(colors.black)
        c.drawString(bx + 7, y - 25, fit(label, "Helvetica", 7, bw - 10))
        bx += bw + 6
    y -= 42

    # legend
    c.setFont("Helvetica-Bold", 8)
    c.setFillColor(colors.black)
    c.drawString(M, y, "Legend")
    y -= 11
    legend = [("ok", "OK: downloaded, or already in the target folder"),
              ("warn", "Warning: no git repo (archive used) or source failed"),
              ("missing", "MISSING: package / version not on ConanCenter"),
              ("error", "Error: recipe could not be fetched"),
              ("pending", "Not processed (run stopped)")]
    lx = M
    c.setFont("Helvetica", 7.5)
    for sev, text in legend:
        w = stringWidth(text, "Helvetica", 7.5) + 22
        if lx + w > W - M:
            lx = M
            y -= 11
        marker(lx + 4, y + 2.5, sev, 3)
        c.setFillColor(colors.black)
        c.drawString(lx + 11, y, text)
        lx += w
    y -= 11
    c.setFillColor(GREY)
    c.drawString(M, y, "[tool] = tool_requires   [test] = test_requires   (CMake) = found in CMakeLists.txt   "
                       "\"see above\" = already expanded earlier")
    y -= 10
    c.setStrokeColor(LINE)
    c.setLineWidth(0.5)
    c.line(M, y, W - M, y)
    y -= 16

    # ---- tree -------------------------------------------------------------
    rows = list(tree_rows(report))
    max_depth = max((r["depth"] for r in rows), default=0)
    indent = min(INDENT, (W - 2 * M - 260) / max(max_depth + 1, 1))
    status_w = 150

    need(ROW)
    c.setFont("Helvetica-Bold", 10)
    c.setFillColor(colors.black)
    c.drawString(M, y, report["root_label"])
    y -= ROW

    if not rows:
        c.setFont("Helvetica-Oblique", 9)
        c.setFillColor(GREY)
        c.drawString(M + 12, y, "(no dependencies)")
        y -= ROW

    for r in rows:
        need(ROW)
        n = r["node"] or {"name": r["key"], "status": ST_PENDING}
        st = n.get("status", ST_PENDING)
        label, _desc, sev = STATUS_INFO.get(st, ("?", "", "pending"))
        x0 = M + 4
        yc = y + 3
        # connectors
        c.setStrokeColor(LINE)
        c.setLineWidth(0.6)
        for lvl, last in enumerate(r["lasts"][:-1]):
            if not last:
                lx = x0 + lvl * indent
                c.line(lx, y - ROW + 7, lx, y + ROW - 3)
        lx = x0 + r["depth"] * indent
        c.line(lx, yc, lx, y + ROW - 3)                       # up to parent
        if not r["lasts"][-1]:
            c.line(lx, yc, lx, y - ROW + 7)                   # down to next sibling
        c.line(lx, yc, lx + indent - 4, yc)                   # across
        mx = lx + indent + 0.5
        marker(mx, yc, sev)

        # text
        tx = mx + 7
        miss = sev in ("missing", "error")
        name_font = "Helvetica-Bold"
        c.setFillColor(SEV_COLOR[sev] if miss else colors.black)
        if r["repeat"] or r["cycle"]:
            name_font = "Helvetica-Oblique"
            c.setFillColor(GREY)
        name = n["name"]
        c.setFont(name_font, 8.8)
        avail = W - M - status_w - tx - 6
        name = fit(name, name_font, 8.8, avail)
        c.drawString(tx, y, name)
        tx += stringWidth(name, name_font, 8.8) + 4
        bits = []
        if n.get("resolved"):
            bits.append(n["resolved"])
        elif n.get("requested"):
            bits.append(f"wanted {n['requested']}")
        if r["kind"] == "tool_requires":
            bits.append("[tool]")
        elif r["kind"] == "test_requires":
            bits.append("[test]")
        if n.get("via") == "cmake":
            bits.append("(CMake)")
        if r["repeat"]:
            bits.append("- see above")
        if r["cycle"]:
            bits.append("- cycle")
        c.setFont("Helvetica", 8)
        c.setFillColor(GREY if not miss else SEV_COLOR[sev])
        c.drawString(tx, y, fit("  ".join(bits), "Helvetica", 8, max(W - M - status_w - tx - 6, 10)))
        if miss and not (r["repeat"] or r["cycle"]):     # strike-through-free underline for emphasis
            c.setStrokeColor(SEV_COLOR[sev])
            c.setLineWidth(0.5)
            c.line(mx + 7, y - 2, mx + 7 + stringWidth(name, name_font, 8.8), y - 2)

        # status label at right
        if sev != "ok":
            c.setFont("Helvetica-Bold", 7.5)
            c.setFillColor(SEV_COLOR[sev])
            c.drawRightString(W - M, y, label)
        else:
            c.setFont("Helvetica", 7.5)
            c.setFillColor(GREY)
            src = "already exists" if st == ST_EXISTS else (n.get("source") or "")
            c.drawRightString(W - M, y, fit(src, "Helvetica", 7.5, status_w))
        y -= ROW

    # ---- problems list ------------------------------------------------------
    from reportlab.lib.utils import simpleSplit
    problem_groups = [(t, d, g) for t, d, g in report_sections(report)
                      if g and not t.startswith(("Successful", "Already"))]
    if problem_groups:
        need(60)
        y -= 10
        c.setFont("Helvetica-Bold", 12)
        c.setFillColor(colors.black)
        c.drawString(M, y, "Problems")
        y -= 16
        for title, _desc, group in problem_groups:
            need(30)
            sev = STATUS_INFO[group[0]["status"]][2]
            c.setFont("Helvetica-Bold", 9.5)
            c.setFillColor(SEV_COLOR[sev])
            c.drawString(M, y, f"{title} ({len(group)})")
            y -= 13
            for n in group:
                lines = [p for p in n["problems"]] or [STATUS_INFO[n["status"]][1]]
                req_by = ", ".join(n["required_by"]) or "-"
                head = f"{_node_label(n)}   required by {req_by}"
                wrapped = simpleSplit(head, "Helvetica-Bold", 8.5, W - 2 * M - 14)
                body = []
                for p in lines:
                    body += simpleSplit(p, "Helvetica", 8, W - 2 * M - 24)
                need(ROW * (len(wrapped) + len(body)) * 0.85 + 4)
                marker(M + 4, y + 3, sev, 3)
                c.setFillColor(colors.black)
                c.setFont("Helvetica-Bold", 8.5)
                for i, ln in enumerate(wrapped):
                    c.drawString(M + 12, y, ln)
                    y -= 11
                c.setFont("Helvetica", 8)
                c.setFillColor(colors.HexColor("#424242"))
                for ln in body:
                    need(11)
                    c.drawString(M + 22, y, ln)
                    y -= 10
                y -= 3
            y -= 6
    c.showPage()
    c.save()


def write_reports(walker: "Walker", recipe: Path, out_dir: Path, pdf: bool = True,
                  log: Callable[[str], None] = print) -> tuple[dict, dict]:
    """Write conanwalker_report.txt/.json and dependency_tree.pdf into out_dir.
    Returns (report, {kind: path})."""
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    report = walker.report(recipe)
    paths = {}
    p = out_dir / "conanwalker_report.txt"
    write_text_report(report, p)
    paths["txt"] = p
    p = out_dir / "conanwalker_report.json"
    p.write_text(json.dumps(report, indent=2), encoding="utf-8")
    paths["json"] = p
    if pdf:
        p = out_dir / "dependency_tree.pdf"
        try:
            write_pdf_tree(report, p)
            paths["pdf"] = p
        except ImportError:
            log("PDF not written: reportlab is not installed (pip install reportlab)")
        except PermissionError:
            log(f"PDF not written: {p} is open in another program - close it and save again")
    return report, paths


# --------------------------------------------------------------------------- #
#  GUI
# --------------------------------------------------------------------------- #
def run_gui():
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox

    class App(tk.Tk):
        COLS = ("spec", "resolved", "kind", "via", "parent", "recipe", "repo", "state")

        def __init__(self):
            super().__init__()
            self.title(f"{APP_NAME} {APP_VERSION}")
            self.geometry("1100x720")
            self.minsize(900, 560)
            self.events: queue.Queue = queue.Queue()
            self.cancel = threading.Event()
            self.worker: Optional[threading.Thread] = None
            self.roots: list[Requirement] = []
            self.last_report: Optional[dict] = None
            self.last_paths: dict = {}
            self._build_menu()
            self._build()
            self.after(100, self._pump)
            self._load_settings()
            self.protocol("WM_DELETE_WINDOW", self._on_close)

        # ---- menu --------------------------------------------------------
        def _build_menu(self):
            mb = tk.Menu(self)
            fm = tk.Menu(mb, tearoff=0)
            fm.add_command(label="Open recipe...", command=self._pick_recipe, accelerator="Ctrl+O")
            fm.add_command(label="Choose target folder...", command=self._pick_target)
            fm.add_separator()
            fm.add_command(label="Save report...", command=self._save_report, accelerator="Ctrl+S")
            fm.add_command(label="Open dependency tree PDF", command=self._open_pdf)
            fm.add_command(label="Open target folder", command=self._open_target)
            fm.add_separator()
            fm.add_command(label="Exit", command=self._on_close)
            mb.add_cascade(label="File", menu=fm)
            hm = tk.Menu(mb, tearoff=0)
            hm.add_command(label="About this software", command=self._about)
            hm.add_command(label="License (GPL v3)", command=self._show_license)
            mb.add_cascade(label="Help", menu=hm)
            self.config(menu=mb)
            self.bind_all("<Control-o>", lambda e: self._pick_recipe())
            self.bind_all("<Control-s>", lambda e: self._save_report())
            self.bind_all("<F1>", lambda e: self._about())

        def _about(self):
            win = tk.Toplevel(self)
            win.title(f"About {APP_NAME}")
            win.resizable(False, False)
            win.transient(self)
            frm = ttk.Frame(win, padding=18)
            frm.pack(fill="both", expand=True)
            ttk.Label(frm, text=APP_NAME, font=("Segoe UI", 18, "bold")).pack(anchor="w")
            ttk.Label(frm, text=f"Version {APP_VERSION}").pack(anchor="w")
            ttk.Label(frm, text="Fetches ConanCenter recipes and upstream source code for every "
                                "dependency of a Conan recipe, and prints the dependency tree.",
                      wraplength=440, justify="left").pack(anchor="w", pady=(8, 8))
            grid = ttk.Frame(frm)
            grid.pack(anchor="w", fill="x")
            rows = (("Developer:", DEVELOPER), ("Copyright:", COPYRIGHT), ("License:", LICENSE_NAME),
                    ("Python:", sys.version.split()[0]))
            for i, (k, v) in enumerate(rows):
                ttk.Label(grid, text=k, font=("Segoe UI", 9, "bold")).grid(row=i, column=0, sticky="nw", padx=(0, 8))
                ttk.Label(grid, text=v, wraplength=340, justify="left").grid(row=i, column=1, sticky="w")
            ttk.Separator(frm).pack(fill="x", pady=10)
            ttk.Label(frm, text=LICENSE_NOTICE, wraplength=440, justify="left",
                      font=("Segoe UI", 8)).pack(anchor="w")
            b = ttk.Frame(frm)
            b.pack(fill="x", pady=(12, 0))
            ttk.Button(b, text="Close", command=win.destroy).pack(side="right")
            ttk.Button(b, text="View license", command=self._show_license).pack(side="right", padx=6)
            win.bind("<Escape>", lambda e: win.destroy())
            win.grab_set()

        def _show_license(self):
            lic = Path(__file__).resolve().parent / "LICENSE"
            try:
                text = lic.read_text(encoding="utf-8")
            except OSError:
                text = (f"{APP_NAME} - {COPYRIGHT}\n\n{LICENSE_NOTICE}\n\nThe LICENSE file was not "
                        f"found next to the program. Full text: {LICENSE_URL}")
            win = tk.Toplevel(self)
            win.title("GNU General Public License v3")
            win.geometry("680x600")
            win.transient(self)
            t = tk.Text(win, wrap="word", font=("Consolas", 9), padx=8, pady=8)
            sb = ttk.Scrollbar(win, orient="vertical", command=t.yview)
            t.configure(yscrollcommand=sb.set)
            sb.pack(side="right", fill="y")
            t.pack(fill="both", expand=True)
            t.insert("1.0", text)
            t.config(state="disabled")
            win.bind("<Escape>", lambda e: win.destroy())

        # ---- layout ------------------------------------------------------
        def _build(self):
            pad = {"padx": 6, "pady": 4}
            top = ttk.Frame(self)
            top.pack(fill="x", **pad)
            top.columnconfigure(1, weight=1)

            self.recipe_var = tk.StringVar()
            self.target_var = tk.StringVar()
            ttk.Label(top, text="Conan recipe:").grid(row=0, column=0, sticky="w")
            ttk.Entry(top, textvariable=self.recipe_var).grid(row=0, column=1, sticky="ew", padx=4)
            ttk.Button(top, text="Open...", command=self._pick_recipe).grid(row=0, column=2)
            ttk.Label(top, text="Target folder:").grid(row=1, column=0, sticky="w", pady=4)
            ttk.Entry(top, textvariable=self.target_var).grid(row=1, column=1, sticky="ew", padx=4)
            ttk.Button(top, text="Browse...", command=self._pick_target).grid(row=1, column=2)

            opt = ttk.LabelFrame(self, text="Options")
            opt.pack(fill="x", **pad)
            self.transitive = tk.BooleanVar(value=True)
            self.cmake_fallback = tk.BooleanVar(value=True)
            self.cmake_always = tk.BooleanVar(value=False)
            self.tool_req = tk.BooleanVar(value=True)
            self.test_req = tk.BooleanVar(value=False)
            self.overwrite = tk.BooleanVar(value=False)
            self.shallow = tk.BooleanVar(value=True)
            self.recipe_src = tk.StringVar(value="git")
            self.source_mode = tk.StringVar(value="git")
            self.token = tk.StringVar()

            r0 = ttk.Frame(opt)
            r0.pack(fill="x", padx=4, pady=2)
            ttk.Checkbutton(r0, text="Follow the whole dependency chain", variable=self.transitive).pack(side="left")
            ttk.Checkbutton(r0, text="Include tool_requires", variable=self.tool_req).pack(side="left", padx=10)
            ttk.Checkbutton(r0, text="Include test_requires", variable=self.test_req).pack(side="left")
            ttk.Checkbutton(r0, text="Overwrite existing folders", variable=self.overwrite).pack(side="left", padx=10)

            rc = ttk.Frame(opt)
            rc.pack(fill="x", padx=4, pady=2)
            ttk.Checkbutton(rc, text="Use CMakeLists.txt when a recipe lists no dependencies",
                            variable=self.cmake_fallback).pack(side="left")
            ttk.Checkbutton(rc, text="Always scan CMakeLists.txt too",
                            variable=self.cmake_always).pack(side="left", padx=10)

            r1 = ttk.Frame(opt)
            r1.pack(fill="x", padx=4, pady=2)
            ttk.Label(r1, text="Recipes from:").pack(side="left")
            ttk.Radiobutton(r1, text="git sparse clone (cached)", value="git", variable=self.recipe_src).pack(side="left")
            ttk.Radiobutton(r1, text="GitHub API", value="api", variable=self.recipe_src).pack(side="left", padx=(0, 20))
            ttk.Label(r1, text="Source:").pack(side="left")
            ttk.Radiobutton(r1, text="git clone (fallback: archive)", value="git", variable=self.source_mode).pack(side="left")
            ttk.Radiobutton(r1, text="archive only", value="archive", variable=self.source_mode).pack(side="left")
            ttk.Radiobutton(r1, text="skip", value="skip", variable=self.source_mode).pack(side="left")
            ttk.Checkbutton(r1, text="shallow (depth 1)", variable=self.shallow).pack(side="left", padx=10)

            r2 = ttk.Frame(opt)
            r2.pack(fill="x", padx=4, pady=2)
            ttk.Label(r2, text="GitHub token (optional, for API rate limits):").pack(side="left")
            ttk.Entry(r2, textvariable=self.token, show="*", width=40).pack(side="left", padx=4)
            self.write_report = tk.BooleanVar(value=True)
            ttk.Checkbutton(r2, text="When finished, save report + PDF dependency tree in target folder",
                            variable=self.write_report).pack(side="left", padx=14)

            btns = ttk.Frame(self)
            btns.pack(fill="x", **pad)
            self.parse_btn = ttk.Button(btns, text="Parse recipe", command=self._parse)
            self.parse_btn.pack(side="left")
            self.start_btn = ttk.Button(btns, text="Start", command=self._start)
            self.start_btn.pack(side="left", padx=6)
            self.stop_btn = ttk.Button(btns, text="Stop", command=self._stop, state="disabled")
            self.stop_btn.pack(side="left")
            ttk.Button(btns, text="Open target folder", command=self._open_target).pack(side="left", padx=6)
            self.report_btn = ttk.Button(btns, text="Save report...", command=self._save_report,
                                         state="disabled")
            self.report_btn.pack(side="left")
            self.pdf_btn = ttk.Button(btns, text="Open PDF tree", command=self._open_pdf, state="disabled")
            self.pdf_btn.pack(side="left", padx=6)
            self.pb = ttk.Progressbar(btns, mode="determinate")
            self.pb.pack(side="left", fill="x", expand=True, padx=6)
            self.pb_label = ttk.Label(btns, text="", width=10)
            self.pb_label.pack(side="left")

            panes = ttk.PanedWindow(self, orient="vertical")
            panes.pack(fill="both", expand=True, **pad)

            tf = ttk.Frame(panes)
            self.tree = ttk.Treeview(tf, columns=self.COLS, show="tree headings", height=10)
            self.tree.heading("#0", text="Dependency")
            self.tree.column("#0", width=170)
            widths = {"spec": 110, "resolved": 90, "kind": 90, "via": 70, "parent": 150, "recipe": 60,
                      "repo": 70, "state": 260}
            for c in self.COLS:
                self.tree.heading(c, text=c.capitalize())
                self.tree.column(c, width=widths[c], stretch=(c == "state"))
            sb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
            self.tree.configure(yscrollcommand=sb.set)
            self.tree.pack(side="left", fill="both", expand=True)
            sb.pack(side="right", fill="y")
            panes.add(tf, weight=1)

            lf = ttk.Frame(panes)
            self.logbox = tk.Text(lf, height=12, wrap="none", font=("Consolas", 9))
            lsb = ttk.Scrollbar(lf, orient="vertical", command=self.logbox.yview)
            self.logbox.configure(yscrollcommand=lsb.set, state="disabled")
            self.logbox.pack(side="left", fill="both", expand=True)
            lsb.pack(side="right", fill="y")
            panes.add(lf, weight=1)

        # ---- actions -----------------------------------------------------
        def _pick_recipe(self):
            p = filedialog.askopenfilename(title="Open Conan recipe", filetypes=[
                ("Conan recipes / CMake", "conanfile.py conanfile.txt CMakeLists.txt"), ("Python", "*.py"),
                ("Text", "*.txt"), ("All files", "*.*")])
            if p:
                self.recipe_var.set(p)
                self._parse()

        def _pick_target(self):
            p = filedialog.askdirectory(title="Choose target folder")
            if p:
                self.target_var.set(p)

        def _open_target(self):
            t = self.target_var.get().strip()
            if t and Path(t).is_dir():
                if os.name == "nt":
                    os.startfile(t)
                elif sys.platform == "darwin":
                    subprocess.Popen(["open", t])
                else:
                    subprocess.Popen(["xdg-open", t])

        def _parse(self) -> bool:
            path = self.recipe_var.get().strip()
            if not path or not Path(path).is_file():
                messagebox.showerror(APP_NAME, "Choose a conanfile.py, conanfile.txt or CMakeLists.txt first.")
                return False
            try:
                self.roots, warns = parse_root(Path(path), self.cmake_fallback.get(), self.cmake_always.get())
            except SyntaxError as e:
                messagebox.showerror(APP_NAME, f"Could not parse the recipe:\n{e}")
                return False
            self.tree.delete(*self.tree.get_children())
            for r in self.roots:
                self._set_status(r.name, {"spec": r.spec or "latest", "kind": r.kind, "via": r.via,
                                          "parent": r.parent, "state": "pending"})
            self._log(f"Parsed {path}: {len(self.roots)} direct dependencies")
            for w in warns:
                self._log(f"  {w}")
            return True

        def _start(self):
            if yaml is None:
                messagebox.showerror(APP_NAME, "PyYAML is required.\n\npip install pyyaml")
                return
            target = self.target_var.get().strip()
            if not target:
                messagebox.showerror(APP_NAME, "Choose a target folder.")
                return
            if not self._parse():
                return
            if not self.roots:
                messagebox.showinfo(APP_NAME, "No dependencies found in this recipe.")
                return
            if (self.recipe_src.get() == "git" or self.source_mode.get() == "git") and not git_available():
                if not messagebox.askyesno(APP_NAME, "git was not found on PATH.\n\nContinue using the "
                                           "GitHub API for recipes and archives for sources?"):
                    return
                self.recipe_src.set("api")
                self.source_mode.set("archive")
            opts = Options(target=Path(target), transitive=self.transitive.get(),
                           include_tool_requires=self.tool_req.get(),
                           include_test_requires=self.test_req.get(),
                           cmake_fallback=self.cmake_fallback.get(),
                           cmake_always=self.cmake_always.get(),
                           recipe_source=self.recipe_src.get(), source_mode=self.source_mode.get(),
                           shallow=self.shallow.get(), overwrite=self.overwrite.get(),
                           github_token=self.token.get().strip(),
                           write_report=self.write_report.get())
            self._save_settings()
            self.cancel.clear()
            self._busy(True)
            roots = list(self.roots)
            recipe = Path(self.recipe_var.get().strip())

            def work():
                ev = self.events
                walker = Walker(opts, lambda m: ev.put(("log", m)),
                                lambda n, d: ev.put(("status", n, d)),
                                lambda a, b: ev.put(("progress", a, b)), self.cancel)
                try:
                    s = walker.run(roots)
                    ev.put(("log", f"\nFinished: {s['ok']} ok, {s['warn']} with warnings, "
                                   f"{s['error']} errors, {s['skipped']} CMake names skipped."))
                except Cancelled:
                    ev.put(("log", "\nStopped."))
                except Exception as e:
                    ev.put(("log", f"\nERROR: {e}"))
                finally:
                    try:            # report also covers stopped / failed runs
                        if opts.write_report:
                            rep_, paths = write_reports(walker, recipe, opts.target,
                                                        log=lambda m: ev.put(("log", m)))
                            for k, pth in paths.items():
                                ev.put(("log", f"{k.upper()} report: {pth}"))
                        else:
                            rep_, paths = walker.report(recipe), {}
                        ev.put(("report", rep_, paths))
                    except Exception as e:
                        ev.put(("log", f"Could not write report: {e}"))
                    ev.put(("done",))

            self.worker = threading.Thread(target=work, daemon=True)
            self.worker.start()

        def _open_path(self, p):
            p = str(p)
            if os.name == "nt":
                os.startfile(p)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", p])
            else:
                subprocess.Popen(["xdg-open", p])

        def _open_pdf(self):
            pdf = self.last_paths.get("pdf")
            if pdf and Path(pdf).exists():
                self._open_path(pdf)
            else:
                messagebox.showinfo(APP_NAME, "No dependency tree PDF yet. Run the task first, or use "
                                              "Save report... and choose PDF.")

        def _save_report(self):
            if not self.last_report:
                messagebox.showinfo(APP_NAME, "There is no report yet. Run the task first.")
                return
            p = filedialog.asksaveasfilename(
                title="Save report", defaultextension=".txt",
                initialfile="conanwalker_report.txt",
                filetypes=[("Text report (incl. full log)", "*.txt"), ("JSON report", "*.json"),
                           ("Dependency tree PDF (A4)", "*.pdf"), ("Log only", "*.log")])
            if not p:
                return
            try:
                ext = Path(p).suffix.lower()
                if ext == ".json":
                    Path(p).write_text(json.dumps(self.last_report, indent=2), encoding="utf-8")
                elif ext == ".pdf":
                    write_pdf_tree(self.last_report, Path(p))
                elif ext == ".log":
                    Path(p).write_text("\n".join(self.last_report["log"]) + "\n", encoding="utf-8")
                else:
                    write_text_report(self.last_report, Path(p))
                self._log(f"Saved {p}")
            except ImportError:
                messagebox.showerror(APP_NAME, "PDF needs reportlab:\n\npip install reportlab")
            except OSError as e:
                messagebox.showerror(APP_NAME, f"Could not save:\n{e}")

        def _stop(self):
            self.cancel.set()
            self._log("Stopping ...")

        def _busy(self, busy: bool):
            self.start_btn.config(state="disabled" if busy else "normal")
            self.parse_btn.config(state="disabled" if busy else "normal")
            self.stop_btn.config(state="normal" if busy else "disabled")
            if busy:
                self.report_btn.config(state="disabled")
                self.pdf_btn.config(state="disabled")

        # ---- event pump --------------------------------------------------
        def _pump(self):
            try:
                while True:
                    ev = self.events.get_nowait()
                    if ev[0] == "log":
                        self._log(ev[1])
                    elif ev[0] == "status":
                        self._set_status(ev[1], ev[2])
                    elif ev[0] == "progress":
                        done, total = ev[1], max(ev[2], 1)
                        self.pb.config(maximum=total, value=done)
                        self.pb_label.config(text=f"{done}/{total}")
                    elif ev[0] == "report":
                        self.last_report, self.last_paths = ev[1], ev[2]
                        self.report_btn.config(state="normal")
                        self.pdf_btn.config(state="normal" if "pdf" in ev[2] else "disabled")
                    elif ev[0] == "done":
                        self._busy(False)
            except queue.Empty:
                pass
            self.after(100, self._pump)

        def _log(self, msg: str):
            self.logbox.config(state="normal")
            self.logbox.insert("end", msg + "\n")
            self.logbox.see("end")
            self.logbox.config(state="disabled")

        def _set_status(self, name: str, fields: dict):
            if "_rename" in fields:                      # CMake name -> ConanCenter name
                new = fields["_rename"]
                if self.tree.exists(name):
                    vals = self.tree.item(name, "values")
                    self.tree.delete(name)
                    if not self.tree.exists(new):
                        self.tree.insert("", "end", iid=new, text=new, values=vals)
                return
            if not self.tree.exists(name):
                self.tree.insert("", "end", iid=name, text=name, values=[""] * len(self.COLS))
            vals = list(self.tree.item(name, "values"))
            for k, v in fields.items():
                if k in self.COLS:
                    vals[self.COLS.index(k)] = v
            self.tree.item(name, values=vals)
            self.tree.see(name)

        # ---- settings ----------------------------------------------------
        def _settings_file(self) -> Path:
            return CACHE_DIR / "settings.json"

        def _load_settings(self):
            try:
                s = json.loads(self._settings_file().read_text(encoding="utf-8"))
            except Exception:
                return
            self.recipe_var.set(s.get("recipe", ""))
            self.target_var.set(s.get("target", ""))
            for key, var in (("transitive", self.transitive), ("tool_req", self.tool_req),
                             ("test_req", self.test_req), ("shallow", self.shallow),
                             ("cmake_fallback", self.cmake_fallback), ("cmake_always", self.cmake_always),
                             ("write_report", self.write_report),
                             ("recipe_src", self.recipe_src), ("source_mode", self.source_mode)):
                if key in s:
                    var.set(s[key])

        def _save_settings(self):
            s = {"recipe": self.recipe_var.get(), "target": self.target_var.get(),
                 "transitive": self.transitive.get(), "tool_req": self.tool_req.get(),
                 "test_req": self.test_req.get(), "shallow": self.shallow.get(),
                 "cmake_fallback": self.cmake_fallback.get(), "cmake_always": self.cmake_always.get(),
                 "write_report": self.write_report.get(),
                 "recipe_src": self.recipe_src.get(), "source_mode": self.source_mode.get()}
            try:
                CACHE_DIR.mkdir(parents=True, exist_ok=True)
                self._settings_file().write_text(json.dumps(s, indent=2), encoding="utf-8")
            except OSError:
                pass

        def _on_close(self):
            self.cancel.set()
            self.destroy()

    App().mainloop()


# --------------------------------------------------------------------------- #
#  CLI
# --------------------------------------------------------------------------- #
def run_cli(argv) -> int:
    p = argparse.ArgumentParser(prog="conanwalker", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--cli", action="store_true", help="run without the GUI")
    p.add_argument("recipe", help="conanfile.py, conanfile.txt or CMakeLists.txt")
    p.add_argument("target", nargs="?", help="target folder (omit with --list)")
    p.add_argument("--list", action="store_true", help="only print parsed dependencies")
    p.add_argument("--no-transitive", action="store_true", help="only direct dependencies")
    p.add_argument("--no-cmake", action="store_true", help="never scan CMakeLists.txt")
    p.add_argument("--cmake-always", action="store_true", help="scan CMakeLists.txt even when the recipe has deps")
    p.add_argument("--no-tool-requires", action="store_true")
    p.add_argument("--test-requires", action="store_true")
    p.add_argument("--recipes-from", choices=["git", "api"], default="git")
    p.add_argument("--source", choices=["git", "archive", "skip"], default="git")
    p.add_argument("--full-history", action="store_true")
    p.add_argument("--overwrite", action="store_true")
    p.add_argument("--no-report", action="store_true", help="don't write report/PDF to the target")
    p.add_argument("--no-pdf", action="store_true", help="write the text/JSON report but no PDF")
    p.add_argument("--version", action="version",
                   version=f"{APP_NAME} {APP_VERSION} - {COPYRIGHT} - {LICENSE_NAME}")
    p.add_argument("--token", default=os.environ.get("GITHUB_TOKEN", ""))
    a = p.parse_args(argv)

    reqs, warns = parse_root(Path(a.recipe), not a.no_cmake, a.cmake_always)
    for w in warns:
        print("warning:", w)
    if a.list or not a.target:
        for r in reqs:
            extra = f"   ({r.raw})" if r.via == "cmake" else ""
            print(f"{r.kind:14} {r.name:28} {r.spec or 'latest':16}{extra}")
        return 0
    opts = Options(target=Path(a.target), transitive=not a.no_transitive,
                   cmake_fallback=not a.no_cmake, cmake_always=a.cmake_always,
                   include_tool_requires=not a.no_tool_requires,
                   include_test_requires=a.test_requires, recipe_source=a.recipes_from,
                   source_mode=a.source, shallow=not a.full_history, overwrite=a.overwrite,
                   github_token=a.token)
    cancel = threading.Event()
    w = Walker(opts, print, lambda n, d: None,
               lambda x, y: None, cancel)
    code = 0
    try:
        s = w.run(reqs)
        print(f"\nFinished: {s['ok']} ok, {s['warn']} with warnings, {s['error']} errors, "
              f"{s['skipped']} CMake names skipped.")
        code = 1 if s["error"] else 0
    except KeyboardInterrupt:
        cancel.set()
        w.outcome, w.finished = "stopped by user", time.time()
        code = 130
    except Exception as e:
        print(f"ERROR: {e}")
        code = 2
    if not a.no_report:
        _, paths = write_reports(w, Path(a.recipe), opts.target, pdf=not a.no_pdf)
        for k, pth in paths.items():
            print(f"{k.upper()} report: {pth}")
    return code


if __name__ == "__main__":
    if len(sys.argv) > 1:
        sys.exit(run_cli([x for x in sys.argv[1:]]))
    run_gui()
