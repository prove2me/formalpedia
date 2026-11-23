-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_jump_split
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_jump_split
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:28:27.467845+00:00
-- url     : https://prove2.me/theorems/6faac4c9-90fd-4fca-89e1-1a152c4d9fc0
-- title:
--   Compensated negative jump integral split at minus one
-- statement:
--   The normalized compensated exponential jump integral over the negative half-line splits into the small negative jumps in (-1,0) and the large negative jumps in (-infinity,-1], with the compensation term present only on the first part.
-- source:
--   Measure-generic set decomposition extracted from the unbounded-variation Lemma 8.6 proof, using the exact indicator convention of the compensated kernel.

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
noncomputable section

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_jump_split
    (μ : Measure ℝ) (θ : ℝ) :
    (∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 - (if -1 < y then θ * y else 0)) / θ ∂μ) =
      (∫ y in Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1 - θ * y) / θ ∂μ) +
      (∫ y in Iic (-1 : ℝ), (Real.exp (θ * y) - 1) / θ ∂μ) := by
  sorry
