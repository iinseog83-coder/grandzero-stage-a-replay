#!/usr/bin/env python3
"""
GRANDZERO Ω — Stage A (M1-P0 R3) Hardened External Replay Verifier (v2)
=======================================================================
Satisfies all 5 pre-execution audit requirements:
  1. Fail-fast SHA-256 verification of ZIP + all 10 internal files BEFORE build.
  2. Explicit Zip-Slip / symlink / unexpected-entry defense inside isolated temp dir.
  3. Strict fail-closed conjunction across HashMatch, CleanBuildPass,
     AuditVectorsPass, AxiomAuditPass (strict axiom whitelist), & SourceIdentityPass.
  4. `#check @GrandZero.StageA.<thm>` and `#print axioms GrandZero.StageA.<thm>`
     bound strictly to the frozen `StageA` modules.
  5. Preserves full raw logs, OS release details, and GitHub Actions run metadata
     so reviewers inspect raw Lean outputs directly rather than trusting this script.
"""

import datetime
import hashlib
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

ARCHIVE_NAME = "GRANDZERO_STAGE_A_M1P0_R3_CLEANROOM_SOURCE_ARCHIVE.zip"
EXPECTED_ARCHIVE_SIZE = 39350
EXPECTED_ARCHIVE_SHA256 = "9755ec152989979c8c519b54261c88cbf8aa46b84757636d4212b68dc2388d51"
EXPECTED_LEAN_VERSION_SUBSTR = "4.33.1"
EXPECTED_LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

EXPECTED_FILE_PINS = {
    "lean-toolchain": "3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71",
    "lakefile.lean": "03d8549b74bd68a8301362fd7ff438abb1f83763ed789b8cf9cace5452daa3b7",
    "lake-manifest.json": "b339d7ce53c132a0b56947e27c9f1a3dbb5d2bd97ba9137093151e244378f027",
    "StageA.lean": "15592e37e2bf4db61de644e33ab8c2d69ce20949021401996c9e3495b3b586fb",
    "Main.lean": "cd972bf55f9d13a5c4c01a609840066ea4cd5b1d5db10518c4b635e9baaf6876",
    "StageA/Q0SyntaxAndUnits.lean": "04ec42ab65c6db2192c7bc5b04010c840f5d61c1e1abdc49f938fe6a645ad807",
    "StageA/Q0PartialSemantics.lean": "3a4e83073c7b2633f86d24dc67bb8b8f9c6731a0d73d09aa35c8fb9478c90469",
    "StageA/Q0ValidTape.lean": "9bc851eb9d938972caac2e77af9d1ecf41009393fc2ff43e37b4535ccd06eade",
    "StageA/Q0GuardedReflection.lean": "aad43e6c1dceeec4bea83781a76b77ccf38926a52003dea296d08f3517035fc9",
    "StageA/Q0BipolarKernel.lean": "bb59274b895c5022741c0e3bb4949ef03881db5f42ad552f52fd634838b31593",
}

THEOREMS_31 = [
    "lem_substUnit",
    "lem_substGuardUnit",
    "lem_substDenote",
    "trapA_nested_div_zero_blocked",
    "lem_reify_exact",
    "po_tape_deps_letBind",
    "po_tape_locality",
    "po_tape_equiv",
    "thm_gpr_unit_sound",
    "thm_gpr_typed_total",
    "cor_gpr_fail_iff_untyped",
    "thm_gpr_value_sound",
    "thm_gpr_domain_exact",
    "thm_tape_gpr_unit_sound",
    "thm_tape_gpr_value_sound",
    "po_tape_locality_reflect",
    "thm_ast_tape_gpr_commute",
    "thm_guard_proof_sound",
    "thm_syndrome_sound",
    "thm_accepted_wellTyped_guardSafe_sound",
    "thm_l05_bipolar",
    "xt01_unprovable_all_certs",
    "xt02_unprovable_all_certs",
    "xt03_expected_pass_tape",
    "xt04_unprovable_all_certs",
    "xt05_unprovable_all_certs",
    "xt06_expected_pass_raw_ssa_with_dead_row",
    "traceA_commutes_and_passes",
    "traceB_ast_and_ssa_pass",
    "traceC_dead_row_passes",
    "traceC_strict_let_unprovable_all_certs",
]


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1048576), b""):
            h.update(chunk)
    return h.hexdigest()


def read_os_release() -> str:
    if os.path.isfile("/etc/os-release"):
        try:
            with open("/etc/os-release", "r", encoding="utf-8") as f:
                for line in f:
                    if line.startswith("PRETTY_NAME="):
                        return line.split("=", 1)[1].strip().strip('"')
        except OSError:
            pass
    return platform.platform()


def find_bin(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    elan_candidate = os.path.join(os.path.expanduser("~"), ".elan", "bin", name)
    if os.path.isfile(elan_candidate):
        return elan_candidate
    if os.path.isfile(elan_candidate + ".exe"):
        return elan_candidate + ".exe"
    raise FileNotFoundError(f"Required executable `{name}` not found on PATH or ~/.elan/bin")


def safe_extract_zip(zip_path: str, dest_dir: str) -> list[str]:
    """Member-by-member extraction blocking Zip-Slip, absolute paths, and symlinks."""
    dest_real = os.path.realpath(dest_dir)
    extracted = []
    with zipfile.ZipFile(zip_path, "r") as zf:
        for info in zf.infolist():
            rel_name = info.filename
            if info.is_dir():
                raise ValueError(f"Unexpected directory entry in archive: {rel_name}")
            if os.path.isabs(rel_name) or "\\" in rel_name:
                raise ValueError(f"Illegal path format in archive: {rel_name}")
            parts = rel_name.split("/")
            if any(p in ("", ".", "..") for p in parts):
                raise ValueError(f"Path traversal attempt in archive: {rel_name}")
            # Reject Unix symlink mode (0o120000)
            unix_mode = info.external_attr >> 16
            if (unix_mode & 0o170000) == 0o120000:
                raise ValueError(f"Symlink entry forbidden in archive: {rel_name}")

            target_path = os.path.realpath(os.path.join(dest_real, *parts))
            if os.path.commonpath([dest_real, target_path]) != dest_real:
                raise ValueError(f"Zip-Slip path escape blocked: {rel_name}")

            os.makedirs(os.path.dirname(target_path), exist_ok=True)
            with zf.open(info, "r") as src, open(target_path, "wb") as dst:
                shutil.copyfileobj(src, dst)
            extracted.append(rel_name)
    return sorted(extracted)


def verify_axiom_output(stdout_text: str) -> tuple[bool, list[str]]:
    """Strictly verify all 31 theorem axiom lines exist and use only ALLOWED_AXIOMS."""
    errors = []
    for bad in ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"):
        if bad in stdout_text:
            errors.append(f"Forbidden axiom token detected: {bad}")

    for thm in THEOREMS_31:
        full_name = f"GrandZero.StageA.{thm}"
        pat_some = re.compile(rf"^'{re.escape(full_name)}' depends on axioms: \[(.*?)\]$", re.M)
        pat_none = re.compile(rf"^'{re.escape(full_name)}' does not depend on any axioms$", re.M)
        m_some = pat_some.search(stdout_text)
        m_none = pat_none.search(stdout_text)
        if m_none:
            continue
        if not m_some:
            errors.append(f"Missing `#print axioms` output line for {full_name}")
            continue
        axs = [a.strip() for a in m_some.group(1).split(",") if a.strip()]
        illegal = [a for a in axs if a not in ALLOWED_AXIOMS]
        if illegal:
            errors.append(f"Unexpected axiom(s) on {full_name}: {illegal}")
    return (len(errors) == 0, errors)


def main() -> int:
    here = os.path.dirname(os.path.abspath(__file__))
    zip_path = os.path.join(here, ARCHIVE_NAME)
    receipt_path = os.path.join(here, "STAGE_A_EXTERNAL_REPLAY_RECEIPT.md")
    utc_now = datetime.datetime.now(datetime.timezone.utc).isoformat()

    gh_repo = os.environ.get("GITHUB_REPOSITORY", "LOCAL_OR_NON_GH_HOST")
    gh_run_id = os.environ.get("GITHUB_RUN_ID", "N/A")
    gh_run_num = os.environ.get("GITHUB_RUN_NUMBER", "N/A")
    gh_sha = os.environ.get("GITHUB_SHA", "N/A")
    gh_actor = os.environ.get("GITHUB_ACTOR", "N/A")
    os_pretty = read_os_release()

    if not os.path.isfile(zip_path):
        print(f"FATAL: Missing {ARCHIVE_NAME} in {here}", file=sys.stderr)
        return 2

    # Gate 1A: Fail-fast ZIP size & SHA-256 verification BEFORE extraction
    actual_zip_size = os.path.getsize(zip_path)
    actual_zip_sha = sha256_file(zip_path)
    if actual_zip_size != EXPECTED_ARCHIVE_SIZE or actual_zip_sha != EXPECTED_ARCHIVE_SHA256:
        with open(receipt_path, "w", encoding="utf-8") as out:
            out.write("# `GRANDZERO Ω — Stage A External Independent Replay Receipt (ABORTED)`\n\n")
            out.write(f"- **Verdict**: **`FAIL (ARCHIVE_HASH_OR_SIZE_MISMATCH)`**\n")
            out.write(f"- **Expected**: `{EXPECTED_ARCHIVE_SIZE}` B / `{EXPECTED_ARCHIVE_SHA256}`\n")
            out.write(f"- **Actual**: `{actual_zip_size}` B / `{actual_zip_sha}`\n")
        print("FATAL: Archive SHA-256 or byte size mismatch. Aborting before extraction.", file=sys.stderr)
        return 2

    lean_bin = find_bin("lean")
    lake_bin = find_bin("lake")

    with tempfile.TemporaryDirectory(prefix="gz_stage_a_ext_") as tmp_root:
        work_dir = os.path.join(tmp_root, "stage_a")
        os.makedirs(work_dir, exist_ok=True)

        # Gate 1B: Safe Zip-Slip-protected extraction & exact 10-file pin check BEFORE build
        extracted_names = safe_extract_zip(zip_path, work_dir)
        has_dot_lake_pre = os.path.exists(os.path.join(work_dir, ".lake"))
        exact_file_set = (extracted_names == sorted(EXPECTED_FILE_PINS.keys()))

        pin_rows = []
        pre_pins_ok = exact_file_set and (not has_dot_lake_pre)
        for rel, exp_sha in sorted(EXPECTED_FILE_PINS.items()):
            p = os.path.join(work_dir, *rel.split("/"))
            act_sha = sha256_file(p) if os.path.isfile(p) else "MISSING"
            ok = (act_sha == exp_sha)
            if not ok:
                pre_pins_ok = False
            pin_rows.append((rel, exp_sha, act_sha, ok))

        if not pre_pins_ok:
            with open(receipt_path, "w", encoding="utf-8") as out:
                out.write("# `GRANDZERO Ω — Stage A External Independent Replay Receipt (ABORTED)`\n\n")
                out.write("- **Verdict**: **`FAIL (INTERNAL_SOURCE_PIN_MISMATCH)`**\n")
            print("FATAL: Internal file SHA-256 mismatch. Aborting before build.", file=sys.stderr)
            return 2

        # Gate 2: Exact Lean 4.33.1 Toolchain Check
        lean_ver = subprocess.run([lean_bin, "--version"], cwd=work_dir, capture_output=True, text=True)
        lake_ver = subprocess.run([lake_bin, "--version"], cwd=work_dir, capture_output=True, text=True)
        exact_4331 = (
            lean_ver.returncode == 0
            and EXPECTED_LEAN_VERSION_SUBSTR in lean_ver.stdout
            and EXPECTED_LEAN_COMMIT in lean_ver.stdout
        )

        # Gate 3: Cold Clean Build & Adversarial Vector Execution
        build_res = subprocess.run([lake_bin, "build"], cwd=work_dir, capture_output=True, text=True)
        clean_build_pass = (build_res.returncode == 0)

        exe_res = subprocess.run([lake_bin, "exe", "stage_a_audit"], cwd=work_dir, capture_output=True, text=True)
        audit_vectors_pass = (
            exe_res.returncode == 0
            and "ALL STAGE A ADVERSARIAL & COMMUTATION VECTORS MATCH EXPECTED: TRUE" in exe_res.stdout
        )

        # Gate 4: Frozen-Module `#check` & `#print axioms` Audit (script placed OUTSIDE work_dir)
        inspect_lean = os.path.join(tmp_root, "ext_inspect_frozen_stage_a.lean")
        with open(inspect_lean, "w", encoding="utf-8") as f:
            f.write("import StageA\n\n")
            for thm in THEOREMS_31:
                f.write(f"#check @GrandZero.StageA.{thm}\n")
                f.write(f"#print axioms GrandZero.StageA.{thm}\n")

        inspect_res = subprocess.run(
            [lake_bin, "env", "lean", inspect_lean],
            cwd=work_dir,
            capture_output=True,
            text=True,
        )
        axiom_whitelist_ok, axiom_errors = verify_axiom_output(inspect_res.stdout)
        axiom_audit_pass = (
            inspect_res.returncode == 0
            and inspect_res.stderr.strip() == ""
            and axiom_whitelist_ok
        )

        # Gate 5: Post-Build Source Identity Re-Verification (0-byte source mutation)
        source_identity_pass = (
            sha256_file(zip_path) == EXPECTED_ARCHIVE_SHA256
            and all(
                sha256_file(os.path.join(work_dir, *rel.split("/"))) == exp_sha
                for rel, exp_sha in EXPECTED_FILE_PINS.items()
            )
        )

        external_replay_pass = (
            pre_pins_ok
            and exact_4331
            and clean_build_pass
            and audit_vectors_pass
            and axiom_audit_pass
            and source_identity_pass
        )

        with open(receipt_path, "w", encoding="utf-8") as out:
            out.write("# `GRANDZERO Ω — Stage A External Independent Replay Receipt`\n\n")
            out.write("## 0. Environment & Run Provenance\n")
            out.write(f"- **UTC Timestamp**: `{utc_now}`\n")
            out.write(f"- **OS Release**: `{os_pretty}`\n")
            out.write(f"- **Kernel / Platform**: `{platform.platform()}` (`{platform.machine()}`)\n")
            out.write(f"- **Python Version**: `{platform.python_version()}`\n")
            out.write(f"- **GitHub Repository / Actor**: `{gh_repo}` / `{gh_actor}`\n")
            out.write(f"- **GitHub Workflow Run ID / Number / Commit**: `{gh_run_id}` / `{gh_run_num}` / `{gh_sha}`\n")
            out.write(f"- **Lean Version**: `{lean_ver.stdout.strip()}`\n")
            out.write(f"- **Lake Version**: `{lake_ver.stdout.strip().splitlines()[0] if lake_ver.stdout.strip() else ''}`\n\n")

            out.write("## 1. Five-Conjunct Verdict Summary\n")
            out.write(f"- `HashMatch` (ZIP `{actual_zip_size}` B + `10/10` pre-build pins + no `.lake`): **`{pre_pins_ok}`**\n")
            out.write(f"- `ExactLean4331` (`4.33.1` & commit `{EXPECTED_LEAN_COMMIT[:12]}`): **`{exact_4331}`**\n")
            out.write(f"- `CleanBuildPass` (`lake build` exit `{build_res.returncode}`): **`{clean_build_pass}`**\n")
            out.write(f"- `AuditVectorsPass` (`stage_a_audit` exit `{exe_res.returncode}` + expected banner): **`{audit_vectors_pass}`**\n")
            out.write(f"- `AxiomAuditPass` (`31/31` theorems, exit `{inspect_res.returncode}`, allowed axioms only): **`{axiom_audit_pass}`**\n")
            if axiom_errors:
                out.write(f"  - Axiom errors: `{axiom_errors}`\n")
            out.write(f"- `SourceIdentityPass` (post-build `10/10` source + ZIP SHA-256 unchanged): **`{source_identity_pass}`**\n")
            out.write(f"- **`ExternalReplayPass` (Conjunction)**: **`{'PASS' if external_replay_pass else 'FAIL'}`**\n\n")

            out.write("## 2. 10/10 Internal File SHA-256 Verification Table\n\n")
            out.write("| File | Expected SHA-256 | Actual SHA-256 | Match |\n| :--- | :--- | :--- | :---: |\n")
            for rel, exp_s, act_s, ok in pin_rows:
                out.write(f"| `{rel}` | `{exp_s}` | `{act_s}` | `{ok}` |\n")

            out.write("\n## 3. Raw `lake build` Log\n```text\n")
            out.write(build_res.stdout + build_res.stderr)
            out.write("\n```\n\n## 4. Raw `lake exe stage_a_audit` Log\n```text\n")
            out.write(exe_res.stdout + exe_res.stderr)
            out.write("\n```\n\n## 5. Raw `#check` & `#print axioms` Output (All 31 Frozen `GrandZero.StageA` Theorems)\n```text\n")
            out.write(inspect_res.stdout + inspect_res.stderr)
            out.write("\n```\n")

        print(f"RECEIPT_WRITTEN: {receipt_path}")
        print(f"EXTERNAL_REPLAY_PASS: {external_replay_pass}")
        return 0 if external_replay_pass else 1


if __name__ == "__main__":
    sys.exit(main())
