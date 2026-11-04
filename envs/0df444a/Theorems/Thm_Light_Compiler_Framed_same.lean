-- Prove2me | Theorems.Thm_Light_Compiler_Framed_same
-- name    : Light.Compiler.Framed.same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:08:01.465992+00:00
-- url     : https://prove2.me/theorems/3b1117eb-5822-477a-991d-bbce2fc16284
-- title:
--   Framed: same
-- statement:
--   A memory that differs only in scratch cells represents the same state in the same frame.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L304-L305
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L304-L305

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ : State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List Instr}

theorem Light.Compiler.Framed.same (I : Framed Z σ q m) (A : AgreeOutside (Scratch Z.F) m m') : Framed Z σ q m' := by sorry
