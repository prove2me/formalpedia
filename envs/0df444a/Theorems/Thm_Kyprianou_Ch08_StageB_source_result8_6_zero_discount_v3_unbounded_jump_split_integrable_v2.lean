-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_jump_split_integrable_v2
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_jump_split_integrable_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:44:46.857395+00:00
-- url     : https://prove2.me/theorems/eb9cdbdf-354a-4374-9b59-659cb62fc5bd
-- title:
--   Compensated negative jump integral split at minus one with Levy integrability
-- statement:
--   For a Levy measure with the quadratic integrability bound and a positive Laplace parameter, the normalized compensated exponential jump integral over the negative half-line splits into the small negative jumps in (-1,0) and the large negative jumps in (-infinity,-1].
-- source:
--   Corrected version of the integral split: the original statement omitted the integrability premise needed for Bochner integral additivity. The prove reduction obtains integrability from compensated_integrable and applies integral_union_ae.

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
noncomputable section

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_jump_split_integrable_v2
    (μ : Measure ℝ) (hμ : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ)
    (θ : ℝ) (hθ : 0 < θ) :
    (∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 - (if -1 < y then θ * y else 0)) / θ ∂μ) =
      (∫ y in Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1 - θ * y) / θ ∂μ) +
      (∫ y in Iic (-1 : ℝ), (Real.exp (θ * y) - 1) / θ ∂μ) := by
  sorry
