-- Prove2me | Theorems.Thm_Light_input_loadWords
-- name    : Light.input_loadWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:25:50.431127+00:00
-- url     : https://prove2.me/theorems/d1b1ca53-0e51-4916-8c0e-7494fdf918b1
-- title:
--   Light: input load Words
-- statement:
--   The initial memory holds the input, and zeros in the cells of the two arguments.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L216-L223
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L216-L223

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
variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}

theorem Light.input_loadWords (W : ℕ) {ws : List ℤ} (h0 : 0 ≤ lim.word) (h : ∀ v ∈ ws, |v| ≤ lim.word) :
    Input lim (memOf ws) 0 0 (loadWords W ws) := by sorry
