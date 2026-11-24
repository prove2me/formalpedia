-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_qzero_scale_q_continuity_and_monotonicity
-- name    : Kyprianou.Ch08.StageB.qzero_scale_q_continuity_and_monotonicity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T00:15:44.16639+00:00
-- url     : https://prove2.me/theorems/c8da3cd9-7913-4eab-aa8a-2dbc419778c9
-- title:
--   Zero-discount continuity and discount monotonicity of the source scale family
-- statement:
--   For a source-faithful scale family, W(q,z) tends to W(0,z) as positive q tends to zero for every nonnegative z, and W(r,z) is monotone in the discount r for every nonnegative z.
-- source:
--   Kyprianou (2006), Chapter 8, scale-family convolution series and discount monotonicity.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_convolution_series
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_series_entire
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_origin_discount_invariant
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_nonnegative_all_real
import Theorems.Thm_Kyprianou_Ch08_StageB_source_weighted_series_terms_pointwise_summable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Topology

namespace Kyprianou.Ch08.StageB

/-- Zero-discount continuity and discount monotonicity of the source scale family. -/
theorem qzero_scale_q_continuity_and_monotonicity :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ), HasSourceScaleFamily ψ W →
      (∀ z : ℝ, 0 ≤ z →
        Tendsto (fun n : ℕ => W (((n : ℝ) + 1)⁻¹) z) atTop (𝓝 (W 0 z))) ∧
      (∀ {r s z : ℝ}, 0 ≤ r → 0 ≤ s → r ≤ s → 0 ≤ z → W r z ≤ W s z) := by
  sorry

end Kyprianou.Ch08.StageB
