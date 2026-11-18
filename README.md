# ConanWalker

Developer: **Mahmud Hasan** · Licence: **GPL-3.0-or-later** (see [LICENSE](LICENSE))

A desktop app (Tkinter) that reads a Conan recipe (`conanfile.py` or `conanfile.txt`) and, for every dependency, fetches its ConanCenter recipe and its upstream source code into a target folder:

```
<target>/
  fmt/
    recipe/            conanfile.py, conandata.yml, patches/, test_package/, config.yml
    repo/              upstream source (git checkout of the release tag, or extracted archive)
    dependency.json    requested/resolved version, who required it, where the source came from
  spdlog/
  ...
```

## Requirements
- Python 3.9+ with Tkinter (included in the python.org Windows installer)
- `pip install -r requirements.txt` (PyYAML, reportlab for the PDF)
- Git on PATH (recommended). Without it, use "GitHub API" for recipes and "archive only" for sources.

## Run
```
python conanwalker.py                 # GUI
python conanwalker.py --cli conanfile.py D:\deps                 # headless, full chain
python conanwalker.py --cli CMakeLists.txt D:\deps                # scan a CMake project
#   --no-transitive  --no-cmake  --cmake-always  --source git|archive|skip
python conanwalker.py --cli conanfile.py --list                  # just show parsed deps
```

## How it works
- **Parsing**: the recipe is parsed statically with Python's `ast` module and is never executed. It picks up the `requires` / `tool_requires` / `build_requires` / `test_requires` class attributes and the `self.requires(...)` calls. Calls inside `if self.options...` blocks are included too, so you get a superset of the real dependencies. If a version is computed at runtime (`f"openssl/{self._v}"`), the latest ConanCenter version is used and the log says so.
- **Versions**: exact versions plus Conan 2 ranges (`[>=1.2 <2]`, `[~1.2]`, `[^1.2]`, `a || b`, `[*]`, `include_prerelease`) are resolved against the recipe's `config.yml`.
- **Recipes**: a sparse, blob-less clone of conan-center-index is cached in `~/.conanwalker` and updated on each run. Only `recipes/<name>` is checked out. Alternatively the GitHub contents API is used (60 requests/hour without a token).
- **Sources**: the source URL for the resolved version comes from `conandata.yml`. GitHub/GitLab archive and release URLs are turned into a git checkout of that tag or commit (shallow by default). Any other URL is downloaded, checked against its sha256 and extracted. If git fails, the app falls back to the archive, then to mirror URLs.
- **CMake fallback**: if the recipe declares no dependencies, `CMakeLists.txt` (and `*Config.cmake.in`) next to it is scanned recursively. You can also open a `CMakeLists.txt` directly. Folders for tests, examples, docs, benchmarks and vendored code (`third_party`, `external`, ...) are skipped. The scanner reads `find_package`, `find_dependency`, `pkg_check_modules`, `pkg_search_module`, `FetchContent_Declare` and `CPMAddPackage`.
  - CMake names are matched to ConanCenter recipe names: a built-in table (ZLIB→zlib, CURL→libcurl, libxml-2.0→libxml2, …), then the GitHub owner/repo (nlohmann/json→nlohmann_json), then name variants.
  - System and toolchain packages (Threads, PkgConfig, Python, OpenGL, …) are ignored. Names with no ConanCenter recipe are logged as skipped.
  - CMake versions are only hints: if that version isn't on ConanCenter, the latest is used.
- **Whole chain**: each downloaded recipe is parsed and its dependencies are queued, until nothing new turns up. If a library recipe declares no dependencies, its downloaded source is scanned for CMake dependencies the same way. Tools (`tool_requires` such as cmake, ninja, msys2) are not scanned, because their own build dependencies don't belong to your project. Tick "Always scan CMakeLists.txt too" to scan even when the recipe lists dependencies. When two packages need the same dependency, the first version found is kept and the log notes the conflict.

## Reports
At the end of every run (also when stopped or failed) these files are written to the target folder:

| File | Contents |
|---|---|
| `conanwalker_report.txt` | Summary; sections for missing packages, missing versions, CMake names with no ConanCenter package, missing git repos (archive used), source failures, errors, not processed, successful, and already present; plus an ASCII dependency tree and the full log |
| `conanwalker_report.json` | The same data in machine-readable form (nodes, edges, log) |
| `dependency_tree.pdf` | A printable A4 dependency tree; marker shapes also work in black and white: ● OK, ▲ warning, ☒ missing/error. Missing packages are shown in red, underlined and labelled; a "Problems" list follows the tree |

In the GUI, **Save report...** (File menu or Ctrl+S) saves the report again as .txt, .json, .pdf or .log, and **Open PDF tree** opens the PDF.

## Re-runs
A dependency whose folder already has `dependency.json` and `recipe/`, plus `repo/` (or Source = skip), is **not downloaded again**: ConanCenter isn't contacted and the report lists it as *ALREADY EXISTS*. If only `repo/` is missing, only the source is fetched. Tick **Overwrite existing folders** to force a fresh download. If an existing version doesn't satisfy the requested one, it's kept and the report notes it.

## Licence
ConanWalker is free software, licensed under the GNU General Public License v3.0 or later. You may use, study, share and modify it. Any modified version you distribute must also be licensed under the GPL, with its source code, so it stays free. See `LICENSE`, or **Help → About this software / License** in the app.

## Known limitations
- ConanCenter deletes old versions from `config.yml` over time, so an old pin (e.g. `zlib/1.3.1`) may come back as "version not in ConanCenter". The latest available versions are listed in the log.
- Recipes whose upstream is not an archive URL (rare) need manual handling.
- Both recipe parsing and CMake scanning include optional/conditional dependencies, so expect a superset (e.g. `msys2` gets pulled in by Windows-only build requirements).
- The CMake scan of a dependency only runs when its source was downloaded (Source ≠ skip).
