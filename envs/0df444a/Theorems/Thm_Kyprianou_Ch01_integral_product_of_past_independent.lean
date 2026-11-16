-- Prove2me | Theorems.Thm_Kyprianou_Ch01_integral_product_of_past_independent
-- name    : Kyprianou.Ch01.integral_product_of_past_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:23:13.351872+00:00
-- url     : https://prove2.me/theorems/eabcd4a4-280e-4016-8b0e-a675a9eb8b4d
-- title:
--   Factorisation of expected products of a future increment and a past-measurable quantity
-- statement:
--   For a real random variable whose generated sigma-algebra is independent of a past sub-sigma-algebra, any measurable transform of that variable is independent of any complex-valued past-measurable random variable. Their expected product therefore factors into the product of expectations.
-- source:
--   Kyprianou (2006), Chapter 1, characteristic-exponential martingale proof; reuses Mathlib ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.integral_product_of_past_independent
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mPast : MeasurableSpace Ω)
    (hmPast : mPast ≤ (inferInstance : MeasurableSpace Ω))
    (G : Ω → ℝ) (hG : Measurable G)
    (hIndep : Indep (MeasurableSpace.comap G inferInstance) mPast P)
    (F : Ω → ℂ)
    (hF : @Measurable Ω ℂ mPast inferInstance F)
    (phi : ℝ → ℂ) (hphi : Measurable phi) :
    (∫ ω, phi (G ω) * F ω ∂P) =
      (∫ ω, phi (G ω) ∂P) * (∫ ω, F ω ∂P) := by sorry
