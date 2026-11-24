-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_zscale_continuous
-- name    : Kyprianou.Ch08.StageB.p2m810_zscale_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:12:33.973861+00:00
-- url     : https://prove2.me/theorems/2211f306-bb2b-4a45-805d-58368da873fd
-- title:
--   Z-scale continuous on the nonnegative ray
-- statement:
--   The scale is continuous on the nonnegative ray; extend it continuously by its origin value and integrate.
-- source:
--   Kyprianou (2006), Theorem 8.10.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Z-scale continuous on the nonnegative ray -/
theorem p2m810_zscale_continuous :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W → ∀ q : ℝ, 0 ≤ q →
      ContinuousOn (Zscale q (W q)) (Ici (0 : ℝ)) := by
  sorry
end Kyprianou.Ch08.StageB
