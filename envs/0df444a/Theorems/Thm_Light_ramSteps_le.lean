-- Prove2me | Theorems.Thm_Light_ramSteps_le
-- name    : Light.ramSteps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:25:39.898169+00:00
-- url     : https://prove2.me/theorems/d7261a00-e482-4546-8f26-cf92c1a5e16f
-- title:
--   Light: ram Steps le
-- statement:
--   The time of a compiled program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L161-L167
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L161-L167

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

theorem Light.ramSteps_le (P : Program) (dec : Bool) (c : ℕ) :
    (ramSteps P dec c : ℝ) ≤ (timeConst P dec : ℝ) * (c : ℝ) + timeConst P dec := by sorry
