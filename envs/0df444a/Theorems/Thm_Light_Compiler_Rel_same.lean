-- Prove2me | Theorems.Thm_Light_Compiler_Rel_same
-- name    : Light.Compiler.Rel.same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:07:55.212511+00:00
-- url     : https://prove2.me/theorems/df02cb41-f762-4d2e-b676-a8d5edd711e1
-- title:
--   Rel: same
-- statement:
--   A memory that differs only in scratch cells represents the same state.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L245-L247
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L245-L247

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}

theorem Light.Compiler.Rel.same (R : Rel Z σ q m) (A : AgreeOutside (Scratch Z.F) m m') : Rel Z σ q m' := by sorry
