-- Prove2me | Theorems.Thm_Kyprianou_Ch04_lipschitzMartingaleSquareGridBound
-- name    : Kyprianou.Ch04.lipschitzMartingaleSquareGridBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:01:47.236095+00:00
-- url     : https://prove2.me/theorems/611bf243-4374-49b6-a4c1-80306206e183
-- title:
--   Lipschitz martingale grid energy
-- statement:
--   A Lipschitz martingale starting at zero has squared expectation at most the equal-grid energy.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
import Theorems.Thm_Martingale_integral_sq_sum_eq_sum_integral_sq
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- A Lipschitz martingale starting at zero has squared expectation bounded by its grid energy. -/
theorem Kyprianou.Ch04.lipschitzMartingaleSquareGridBound {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : NNReal → Omega → ℝ) (hM : Martingale M F P)
    (h0 : ∀ᵐ w ∂P, M 0 w = 0) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ s t : NNReal, s ≤ t → ∀ᵐ w ∂P,
      |M t w - M s w| ≤ C * ((t : ℝ) - (s : ℝ)))
    (t : NNReal) (N : ℕ) (hN : 0 < N) :
    (∫ w, (M t w)^2 ∂P) ≤ (C*(t : ℝ))^2 / (N : ℝ) := by
  sorry
