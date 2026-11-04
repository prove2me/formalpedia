-- Prove2me | Theorems.Thm_Light_Compiler_Rel_loc_zero
-- name    : Light.Compiler.Rel.loc_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:41.105107+00:00
-- url     : https://prove2.me/theorems/0d48eeef-c644-47b3-8520-45398ff1cc47
-- title:
--   Rel: loc zero
-- statement:
--   The cell to which FP points is local variable 0.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L285-L286
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L285-L286

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}

theorem Light.Compiler.Rel.loc_zero (R : Rel Z σ q m) (hF : 0 < Z.F) : m (cStack q) = wd W (σ.loc 0) := by sorry
