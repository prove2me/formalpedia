-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_lower_exit_arbitrary_scale
-- name    : Kyprianou.Ch08.StageB.p2m810_lower_exit_arbitrary_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:26:06.022116+00:00
-- url     : https://prove2.me/theorems/d5119ba7-c10c-433e-ac5f-b7a8436c28d2
-- title:
--   Down-before-up formula for an arbitrary source scale family
-- statement:
--   Use the one-sided downward identities for the given exponent and scale family. Substitute them into the stopped downward splitting identity; the coefficient of W cancels. This is the public arbitrary-family version of the proof used in Theorem 8.1.
-- source:
--   Kyprianou (2006), Theorem 8.10(ii), and Theorem 8.1.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Down-before-up formula for an arbitrary source scale family -/
theorem p2m810_lower_exit_arbitrary_scale :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      downBeforeUpExpectation P D.X q x a =
        Zscale q (W q) x - Zscale q (W q) a * W q x / W q a := by
  sorry
end Kyprianou.Ch08.StageB
