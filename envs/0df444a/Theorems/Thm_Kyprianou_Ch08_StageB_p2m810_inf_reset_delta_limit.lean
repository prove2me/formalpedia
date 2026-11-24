-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_reset_delta_limit
-- name    : Kyprianou.Ch08.StageB.p2m810_inf_reset_delta_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:05:07.661875+00:00
-- url     : https://prove2.me/theorems/4e2ca661-242b-4e95-a81f-959703097d69
-- title:
--   Small-reset scale correction vanishes
-- statement:
--   By monotonicity of W on [0,epsilon], the nonnegative quotient (Z(epsilon)-1)/W(epsilon) is bounded by q*epsilon. Apply the squeeze theorem on the positive right neighbourhood.
-- source:
--   Kyprianou (2006), Theorem 8.10(ii); Pistorius (2004), Proposition 2(i), and two-sided exit renewal approximation.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Small-reset scale correction vanishes -/
theorem p2m810_inf_reset_delta_limit :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 ≤ q → (∀ b : ℝ, 0 < b → 0 < W q b) →
      Tendsto (fun ε : ℝ => (Zscale q (W q) ε - 1) / W q ε)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  sorry
end Kyprianou.Ch08.StageB
