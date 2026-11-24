-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_tilt_right_derivative
-- name    : Kyprianou.Ch08.StageB.p2m810_tilt_right_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:05:24.503813+00:00
-- url     : https://prove2.me/theorems/4c816eb5-f2f3-4f57-8a4d-29eeeee31d44
-- title:
--   Right derivative of the exponentially tilted scale
-- statement:
--   Product-rule identity for the right derivative of the tilted scale, including the exact untilted denominator.
-- source:
--   Kyprianou (2006), Theorem 8.10(i); Avram, Kyprianou and Pistorius (2004), section 4, equations (13)-(22).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Right derivative of the exponentially tilted scale -/
theorem p2m810_tilt_right_derivative :
    ∀ (w : ℝ → ℝ) (θ a d : ℝ),
      HasDerivWithinAt w d (Ici a) a →
      HasDerivWithinAt (tiltedScale θ w)
        (derivWithin (tiltedScale θ w) (Ici a) a) (Ici a) a ∧
      derivWithin (tiltedScale θ w) (Ici a) a + θ * tiltedScale θ w a =
        Real.exp (-θ*a) * d := by
  sorry
end Kyprianou.Ch08.StageB
