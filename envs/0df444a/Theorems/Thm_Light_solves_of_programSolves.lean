-- Prove2me | Theorems.Thm_Light_solves_of_programSolves
-- name    : Light.solves_of_programSolves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:25:41.721008+00:00
-- url     : https://prove2.me/theorems/b33864eb-ca72-45a5-9dcb-a79cbe21186c
-- title:
--   Light: solves of program Solves
-- statement:
--   **The compiled program solves the problem on the word RAM**, within C · T + C steps, C depending
--   on the compiled program only.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L237-L250
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L237-L250

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

theorem Light.solves_of_programSolves {prob : Problem} {P : Program} {p0 : ℕ} {dec : Bool} {s k r : ℕ}
    {dom : prob.Inst → Prop} {T : prob.Inst → ℝ} (h : ProgramSolves prob P p0 dec s k dom T)
    (hr : ∀ x, (prob.params x).length ≤ r) :
    Solves prob (compileProgram P p0 dec) (slopeOf P dec s k r) dom
      fun x => (timeConst P dec : ℝ) * T x + timeConst P dec := by sorry
