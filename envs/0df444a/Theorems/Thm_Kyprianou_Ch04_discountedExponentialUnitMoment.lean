-- Prove2me | Theorems.Thm_Kyprianou_Ch04_discountedExponentialUnitMoment
-- name    : Kyprianou.Ch04.discountedExponentialUnitMoment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:43:48.766305+00:00
-- url     : https://prove2.me/theorems/de63c6a4-16e4-447e-86d5-ba1f18ea40fe
-- title:
--   Unit marginal of a discounted exponential martingale
-- statement:
--   A discounted exponential martingale with zero initial driver has integrable unit exponential marginal with expectation equal to the inverse discount. This purely martingale calculation is independent of the Lévy triplet.
-- source:
--   Kyprianou (2006), Exercise 4.3(iv), unconditional martingale expectation.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.discountedExponentialUnitMoment
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hZero : ∀ w, X 0 w = 0)
    (beta lam : Real)
    (hM : Martingale (fun (t : NNReal) w =>
      Real.exp (-lam * (t : Real)) * Real.exp (beta * X t w)) F P) :
    Integrable (fun w => Real.exp (beta * X 1 w)) P ∧
      (∫ w, Real.exp (beta * X 1 w) ∂P) = Real.exp lam := by
  sorry
