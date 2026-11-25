-- Prove2me | Theorems.Thm_Kyprianou_Ch04_monotoneLIntegralBudgetV1
-- name    : Kyprianou.Ch04.monotoneLIntegralBudgetV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:27:09.714906+00:00
-- url     : https://prove2.me/theorems/4d81a609-edb2-57fc-aff7-c31a5c745109
-- title:
--   Increasing nonnegative grid maxima preserve a uniform first moment budget
-- statement:
--   Monotone convergence of nonnegative measurable random variables with uniformly bounded integrals.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); maximal estimate via discrete grids and monotone convergence.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem monotoneLIntegralBudgetV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (K : ℝ)
    (hint : ∀ k, Integrable (f k) P)
    (hmeas : ∀ k, Measurable (f k))
    (hnonneg : ∀ k ω, 0 ≤ f k ω)
    (hmono : ∀ ω, Monotone (fun k => f k ω))
    (hbudget : ∀ k, (∫ ω, f k ω ∂P) ≤ K) :
    (∫⁻ ω, ⨆ k, ENNReal.ofReal (f k ω) ∂P) ≤ ENNReal.ofReal K := by
  sorry
end Kyprianou.Ch04
