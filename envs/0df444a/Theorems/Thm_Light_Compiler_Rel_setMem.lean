-- Prove2me | Theorems.Thm_Light_Compiler_Rel_setMem
-- name    : Light.Compiler.Rel.setMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:42.701244+00:00
-- url     : https://prove2.me/theorems/c1be22a1-27a0-4e95-af78-08b6e22fd133
-- title:
--   Rel: set Mem
-- statement:
--   Writing a memory cell.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L268-L277
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L268-L277

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}

theorem Light.Compiler.Rel.setMem (R : Rel Z σ q m) (hq : 1 ≤ q) {a : ℤ} (ha : Z.lim.Addr a) (v : ℤ) :
    Rel Z { σ with mem := Function.update σ.mem a.toNat v } q (Function.update m a (wd W v)) := by sorry
