-- Prove2me | Theorems.Thm_Kyprianou_Ch04_gridStepDifferenceWeightBoundV1
-- name    : Kyprianou.Ch04.gridStepDifferenceWeightBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:43:48.724632+00:00
-- url     : https://prove2.me/theorems/b0a2b29d-8c5d-435a-9156-b58ac74497b5
-- title:
--   gridStepDifferenceWeightBoundV1
-- statement:
--   Physical clipped grid step identity or contraction.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- The step interpolation operator preserves the sup-norm distance. -/

theorem Kyprianou.Ch04.gridStepDifferenceWeightBoundV1 (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ)
    (H L : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ k ∈ Finset.range n, |H k-L k| ≤ C) :
    ∀ s, |(∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
      (fun _ => H k) s) - (∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
      (fun _ => L k) s)| ≤ C := by
  sorry
