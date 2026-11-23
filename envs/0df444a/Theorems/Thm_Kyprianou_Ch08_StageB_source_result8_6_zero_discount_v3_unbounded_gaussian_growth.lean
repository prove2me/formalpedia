-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_gaussian_growth
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_gaussian_growth
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:36:49.659662+00:00
-- url     : https://prove2.me/theorems/0dd6635d-4e53-4751-be5f-2a9babea75ba
-- title:
--   Gaussian branch eventual growth bound
-- statement:
--   For a positive quadratic coefficient and finite nonnegative large-jump mass, the drift plus quadratic growth and nonnegative compensated small-jump integral eventually exceeds any real constant.
-- source:
--   Measure-generic Gaussian branch extracted from the unbounded-variation Lemma 8.6 proof; the compensated small-jump integrand is nonnegative for positive parameters.

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
noncomputable section

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_gaussian_growth
    (μ : Measure ℝ) (d a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧ ∀ θ : ℝ, β ≤ θ →
      C < d + a * θ +
        (∫ y in Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1 - θ * y) / θ ∂μ) - B / θ := by
  sorry
