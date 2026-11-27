-- Prove2me | Theorems.Thm_Kyprianou_Ch04_gridStepUniformWeightBoundV1
-- name    : Kyprianou.Ch04.gridStepUniformWeightBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:37:36.141691+00:00
-- url     : https://prove2.me/theorems/14de9512-d0d5-495a-aa35-a11c593149c6
-- title:
--   gridStepUniformWeightBoundV1
-- statement:
--   Physical grid kernel estimate.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- Disjoint right-closed monotone grid cells preserve a uniform weight bound,
including points outside the grid. -/

theorem Kyprianou.Ch04.gridStepUniformWeightBoundV1 {Ω : Type} (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ)
    (H : ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ k ∈ Finset.range n, ∀ w, |H k w| ≤ K) :
    ∀ s w, |∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
      (fun _ => H k w) s| ≤ K := by
  sorry
