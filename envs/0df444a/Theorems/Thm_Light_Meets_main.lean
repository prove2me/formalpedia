-- Prove2me | Theorems.Thm_Light_Meets_main
-- name    : Light.Meets.main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:25:23.981123+00:00
-- url     : https://prove2.me/theorems/cfa4fdd1-fa6e-4289-a239-c020cf3d119c
-- title:
--   Meets: main
-- statement:
--   **The outermost statement calls a procedure that meets a specification.**  The call costs four
--   steps, and B is any real bound for the time.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L82-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L82-L90

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

theorem Light.Meets.main {lim : Limits} {P : Program} {p : ℕ} {i j : ℤ} {μ : ℕ → ℤ} {T : ℕ}
    {R : ℤ → (ℕ → ℤ) → Prop} {B : ℝ} (h : Meets lim P p 1 [i, j] μ T R) (hd : 0 < lim.depth)
    (hB : ((T + 4 : ℕ) : ℝ) ≤ B) :
    ∃ (σ' : State) (c : ℕ), Exec lim P 0 (mainStmt p) ⟨frame [0, i, j], μ⟩ σ' c ∧ (c : ℝ) ≤ B ∧
      R (σ'.loc 0) σ'.mem := by sorry
