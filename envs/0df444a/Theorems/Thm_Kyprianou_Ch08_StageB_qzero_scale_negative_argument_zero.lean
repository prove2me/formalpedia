-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_qzero_scale_negative_argument_zero
-- name    : Kyprianou.Ch08.StageB.qzero_scale_negative_argument_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:15:34.8304+00:00
-- url     : https://prove2.me/theorems/999719bf-1035-4009-a5a4-52c3f40ea55d
-- title:
--   Negative-argument zero extension of a source scale family
-- statement:
--   For every nonnegative discount, the source scale value vanishes at every negative argument.
-- source:
--   Kyprianou (2006), Chapter 8, IsQScale negative-argument normalization.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology

namespace Kyprianou.Ch08.StageB

/-- Negative-argument zero extension at every nonnegative discount. -/
theorem qzero_scale_negative_argument_zero :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ), HasSourceScaleFamily ψ W →
      ∀ z : ℝ, z < 0 → ∀ q : ℝ, 0 ≤ q → W q z = 0 := by
  sorry

end Kyprianou.Ch08.StageB
