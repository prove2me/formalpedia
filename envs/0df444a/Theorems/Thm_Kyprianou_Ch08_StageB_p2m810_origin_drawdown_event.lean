-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_origin_drawdown_event
-- name    : Kyprianou.Ch08.StageB.p2m810_origin_drawdown_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:13:45.725454+00:00
-- url     : https://prove2.me/theorems/a8fa3ea2-44dc-487e-8a35-4b18498f4987
-- title:
--   Origin drawdown event equals centred strict crossing
-- statement:
--   The source running maximum equals the supremum over the compact path image, which is nonnegative since the path starts at zero. The strict crossing event is the same by real algebra.
-- source:
--   Kyprianou (2006), Theorem 8.10(i).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Origin drawdown event. -/
theorem p2m810_origin_drawdown_event :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (a : ℝ) (ω : Ω) (t : ℝ≥0),
      a < reflectAtSup X.X 0 t ω ↔
      X.X t ω - sSup ((fun r => X.X r ω) '' Icc 0 t) < -a := by
  sorry
end Kyprianou.Ch08.StageB
