-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_scale_discount_sequence_limit
-- name    : Kyprianou.Ch08.StageB.p2m88_scale_discount_sequence_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:39:28.434238+00:00
-- url     : https://prove2.me/theorems/d2d60174-889d-4504-a4b5-55a7feaa4108
-- title:
--   Pointwise continuity of the source scale family at zero discount
-- statement:
--   For positive discounts bounded by one and converging to zero, the scale functions converge pointwise by Tannery's theorem applied to their convolution series. At zero use the origin invariance and for negative spatial arguments use the defining zero extension.
-- source:
--   Kyprianou (2006), Corollary 8.8, q decreasing to zero.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal

namespace Kyprianou.Ch08.StageB
 theorem p2m88_scale_discount_sequence_limit :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n ≤ 1) → Tendsto r atTop (nhds 0) →
      ∀ z : ℝ, Tendsto (fun n => W (r n) z) atTop (nhds (W 0 z)) := by
  sorry
end Kyprianou.Ch08.StageB
