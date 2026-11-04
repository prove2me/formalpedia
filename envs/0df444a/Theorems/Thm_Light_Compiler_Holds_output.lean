-- Prove2me | Theorems.Thm_Light_Compiler_Holds_output
-- name    : Light.Compiler.Holds.output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:25:27.477386+00:00
-- url     : https://prove2.me/theorems/ee7f044e-4ed1-4390-b05c-0fbb4212bedf
-- title:
--   Holds: output
-- statement:
--   Reading the output: a cell of a memory that holds μ, as a signed word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L226-L229
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L226-L229

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

theorem Light.Compiler.Holds.output {c : ℤ → BitVec W} (h : Holds W lim μ c) {N Q : ℕ}
    (hfit : Fits W lim N Q) (off i : ℕ) : WordRam.output c off i = μ (off + i) := by sorry
