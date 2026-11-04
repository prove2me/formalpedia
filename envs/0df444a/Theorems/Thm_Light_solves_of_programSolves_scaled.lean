-- Prove2me | Theorems.Thm_Light_solves_of_programSolves_scaled
-- name    : Light.solves_of_programSolves_scaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:25:38.37984+00:00
-- url     : https://prove2.me/theorems/1cc0eeac-ecbd-4e4d-a8e6-2a629b670a54
-- title:
--   Light: solves of program Solves scaled
-- statement:
--   The form in which the running-time theorems need it: if the light program takes at most A · T
--   steps and T ≥ 1 on the domain, the compiled program takes at most C · T steps, where
--   C = timeConst · (A + 1).
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L367-L374
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L367-L374

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)

theorem Light.solves_of_programSolves_scaled {prob : Problem} {P : Program} {p0 : ℕ} {dec : Bool}
    {s k r : ℕ} {dom : prob.Inst → Prop} {T : prob.Inst → ℝ} {A : ℝ}
    (h : ProgramSolves prob P p0 dec s k dom fun x => A * T x)
    (hr : ∀ x, (prob.params x).length ≤ r) (h1 : ∀ x, dom x → 1 ≤ T x) :
    Solves prob (compileProgram P p0 dec) (slopeOf P dec s k r) dom
      fun x => ((timeConst P dec : ℝ) * (A + 1)) * T x := by sorry
