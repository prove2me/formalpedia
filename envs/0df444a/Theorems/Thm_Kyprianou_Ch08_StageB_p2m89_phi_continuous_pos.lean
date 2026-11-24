-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_continuous_pos
-- name    : Kyprianou.Ch08.StageB.p2m89_phi_continuous_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:32:52.192957+00:00
-- url     : https://prove2.me/theorems/6ba8b020-d4e2-40aa-9383-2c5d7815bc61
-- title:
--   Continuity of the positive right-root branch from convexity and scale-family roots.
-- statement:
--   Continuity of the positive right-root branch from convexity and scale-family roots.
-- source:
--   Kyprianou (2006), Theorem 8.9: differentiability of the positive right root.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Continuity of the positive right-root branch from convexity and scale-family roots. -/
theorem p2m89_phi_continuous_pos :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      ψ 0 = 0 →
      ConvexOn ℝ (Ici (0 : ℝ)) ψ →
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 < q → ContinuousAt (Phi ψ) q := by
  sorry

end Kyprianou.Ch08.StageB
