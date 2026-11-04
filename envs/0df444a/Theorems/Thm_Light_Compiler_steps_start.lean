-- Prove2me | Theorems.Thm_Light_Compiler_steps_start
-- name    : Light.Compiler.steps_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:59.112775+00:00
-- url     : https://prove2.me/theorems/45720767-35b7-4ac7-86d9-942c5c76629a
-- title:
--   Compiler: steps start
-- statement:
--   From the first instruction to the outermost statement.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StartUp.lean#L237-L253
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StartUp.lean#L237-L253

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StartUp
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

theorem Light.Compiler.steps_start (P : Program) (p0 : ℕ) (dec : Bool) (hneg : InRange W (-1))
    (m : ℤ → BitVec W) :
    Steps (compileProgram P p0 dec) (dispPos P dec + frameSize P + 9) ⟨0, m⟩
      ⟨mainPos, startMem (frameSize P) (dispPos P dec) m⟩ := by sorry
