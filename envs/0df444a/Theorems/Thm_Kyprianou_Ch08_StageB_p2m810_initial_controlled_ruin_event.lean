-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_initial_controlled_ruin_event
-- name    : Kyprianou.Ch08.StageB.p2m810_initial_controlled_ruin_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:15:52.218634+00:00
-- url     : https://prove2.me/theorems/3d7b4d1e-8a0d-4a24-8c5f-841e7e45a9d6
-- title:
--   Initial drawdown crossing equals controlled reserve ruin
-- statement:
--   At positive time use the proved piecewise barrier reserve formula. The source running maximum with initial maximum x equals max x of the Avram running maximum, by the origin reflection bridge and x≥0.
-- source:
--   Kyprianou (2006), Theorem 8.10(i).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Initial drawdown crossing equals controlled reserve ruin -/
theorem p2m810_initial_controlled_ruin_event :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (x a : ℝ) (ω : Ω) (t : ℝ≥0),
      0 ≤ x → x ≤ a → 0 < t →
      (a < reflectAtSup X.X x t ω ↔
        riskProcess X (a-x) (barrierStrategy X (a-x) a) t ω < 0) := by
  sorry
end Kyprianou.Ch08.StageB
