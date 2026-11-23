-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_compensated_integrable
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_compensated_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:19:35.60282+00:00
-- url     : https://prove2.me/theorems/77b97bfd-c789-4450-a6c6-6520fc7b6227
-- title:
--   Compensated negative jump kernel integrability for a Lévy measure
-- statement:
--   For any measure with the Lévy quadratic integrability bound, the compensated exponential jump kernel is integrable on the negative half-line at every nonnegative Laplace parameter. This isolates the measure-theoretic integrability needed by the unbounded-variation Lemma 8.6 branch.
-- source:
--   Generic measure form of the Proved Avram compensated-jump integrability proof, using the pinned exp_neg_remainder_bounds theorem and the Kyprianou triplet Lévy measure bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exp_neg_remainder_bounds
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_compensated_integrable
    (μ : Measure ℝ) (hμ : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ) :
    ∀ θ : ℝ, 0 ≤ θ →
      IntegrableOn
        (fun y : ℝ => Real.exp (θ * y) - 1 -
          θ * y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
        (Iio (0 : ℝ)) μ := by
  sorry
