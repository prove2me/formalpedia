-- Prove2me | Theorems.Thm_Leakage_not_ct_subroutine_ok_branch_on_secret_byte
-- name    : Leakage.not_ct_subroutine_ok_branch_on_secret_byte
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-25T23:56:50.945516+00:00
-- url     : https://prove2.me/theorems/b895839e-1af7-4a67-ad8b-f1f8b222ea95
-- title:
--   A subroutine that branches on a secret byte is not constant-time
-- statement:
--   The judgment `Leakage.ct_subroutine_ok` (bundle `Arm64_Leakage`) is not vacuous: it fails for a four-instruction program that branches on a byte it reads from memory. The program is `Program.ofWords 0x10000 [0x39400001, 0x34000041, 0xd503201f, 0xd65f03c0]`, that is `ldrb w1, [x0]; cbz w1, #8; nop; ret` at address `0x10000`. Hooks reveal no arguments (arity 0 for every name, and the program has none). The precondition, for a ghost byte $b$, is that `x0` points to one owned byte with value $b$; the public-data relation is always true, so $b$ is secret. The theorem says this subroutine, at its entry `0x10000`, is not `ct_subroutine_ok`.
--
--   Two runs whose byte is $0$ and $1$ show it: with $0$ the branch is taken and the run executes `ldrb`, `cbz` and `ret` (instruction addresses `0x10000`, `0x10004`, `0x1000c`); with $1$ it falls through to the `nop` at `0x10008` before the `ret`. The two runs reveal different observations.
-- source:
--   J. B. Almeida, M. Barbosa, G. Barthe, F. Dupressoir, M. Emmi, "Verifying Constant-Time Implementations", 25th USENIX Security Symposium (2016), pp. 53-70, ISBN 978-1-931971-32-4, https://www.usenix.org/conference/usenixsecurity16/technical-sessions/presentation/almeida, non-vacuity of the constant-time judgment: a subroutine that branches on a secret byte is not constant-time

import Definitions.Def_Arm64_Leakage

open Arm64 Leakage

theorem Leakage.not_ct_subroutine_ok_branch_on_secret_byte :
    ¬ ct_subroutine_ok
      (Program.ofWords 0x10000#64 [0x39400001#32, 0x34000041#32, 0xd503201f#32, 0xd65f03c0#32])
      (fun _ => 0) 0x10000#64
      ({ pre := fun b s => s.readReg64 Reg.x0 ↦ₛ [b], post := fun _ _ _ => ⌜True⌝ } : Spec (BitVec 8))
      (fun _ _ => True) := by
  sorry
