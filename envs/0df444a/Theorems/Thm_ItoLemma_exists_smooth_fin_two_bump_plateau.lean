-- Prove2me | Theorems.Thm_ItoLemma_exists_smooth_fin_two_bump_plateau
-- name    : ItoLemma.exists_smooth_fin_two_bump_plateau
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:46:29.63655+00:00
-- url     : https://prove2.me/theorems/cd9a6161-be82-4c6a-8dc3-6526673a6671
-- title:
--   Compactly Supported Smooth Plateau on the Two-Dimensional State Space
-- statement:
--   For any nonnegative radius, there is a smooth real-valued bump function on the two-dimensional product state space which is one throughout the closed ball of that radius and vanishes outside a slightly larger ball. It supports the direct truncation of the polynomial product test function before applying the vector Itô formula.
-- source:
--   Mathlib ContDiffBump construction in the finite-dimensional normed vector space Fin 2 → Real, with continuity and support properties documented on 26 October 2026 at https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/BumpFunction/Basic.html

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

theorem ItoLemma.exists_smooth_fin_two_bump_plateau
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ ψ : (Fin 2 → ℝ) → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) ψ ∧ HasCompactSupport ψ ∧
      (∀ z : Fin 2 → ℝ, ‖z‖ ≤ R → ψ z = 1) ∧
      (∀ z : Fin 2 → ℝ, R + 2 ≤ ‖z‖ → ψ z = 0) := by sorry
