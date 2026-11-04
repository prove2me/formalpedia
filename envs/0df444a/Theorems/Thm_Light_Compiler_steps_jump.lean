-- Prove2me | Theorems.Thm_Light_Compiler_steps_jump
-- name    : Light.Compiler.steps_jump
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:35.881408+00:00
-- url     : https://prove2.me/theorems/08759b92-c539-41f5-8bdc-e9e265f9d69f
-- title:
--   Compiler: steps jump
-- statement:
--   An unconditional jump.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L308-L310
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L308-L310

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ : State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List Instr}

theorem Light.Compiler.steps_jump {l : ℕ} (hcode : CodeAt code pos (.bltz cNEG l :: rest))
    (hneg : m cNEG = wd W (-1)) (hr : InRange W (-1)) : Steps code 1 ⟨pos, m⟩ ⟨l, m⟩ := by sorry
