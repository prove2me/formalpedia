-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ennrealBudgetToRealV1
-- name    : Kyprianou.Ch04.ennrealBudgetToRealV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:27:19.8888+00:00
-- url     : https://prove2.me/theorems/6eccaacc-1535-4bc4-bd5b-adcdcd854385
-- title:
--   Finite extended expectation gives real integrability and budget
-- statement:
--   A measurable extended nonnegative function with finite integral bound has an integrable real representative satisfying the same bound and is finite almost everywhere.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); maximal estimate via discrete grids and monotone convergence.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem ennrealBudgetToRealV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (K : ℝ) (hK : 0 ≤ K)
    (hbudget : (∫⁻ ω, F ω ∂P) ≤ ENNReal.ofReal K) :
    Integrable (fun ω => (F ω).toReal) P ∧
      (∫ ω, (F ω).toReal ∂P) ≤ K ∧
      (∀ᵐ ω ∂P, F ω < ⊤) := by
  sorry
end Kyprianou.Ch04
