-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_scale_discount_unit_bound
-- name    : Kyprianou.Ch08.StageB.p2m88_scale_discount_unit_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:39:26.841899+00:00
-- url     : https://prove2.me/theorems/8fadcb5b-2ff2-48bb-ae71-37a094083f94
-- title:
--   Unit-discount scale function dominates lower discounts
-- statement:
--   All convolution coefficients are nonnegative, hence each term at a discount between zero and one is bounded by the corresponding term at unit discount. Sum the convergent series and handle the origin and negative values separately.
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
 theorem p2m88_scale_discount_unit_bound :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ z q : ℝ, 0 ≤ q → q ≤ 1 → W q z ≤ W 1 z := by
  sorry
end Kyprianou.Ch08.StageB
