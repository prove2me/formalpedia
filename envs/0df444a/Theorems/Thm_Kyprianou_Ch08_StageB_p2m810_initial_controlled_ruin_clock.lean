-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_initial_controlled_ruin_clock
-- name    : Kyprianou.Ch08.StageB.p2m810_initial_controlled_ruin_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:15:47.572667+00:00
-- url     : https://prove2.me/theorems/2923690c-73ba-4b27-a3b2-cbb4cb627a8a
-- title:
--   Initial source drawdown clock equals controlled ruin clock
-- statement:
--   The controlled negative reserve and the strict source drawdown event coincide at positive times. The initial reserve is nonnegative, so the all-time ruin infimum and the positive-time crossing infimum coincide.
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
/-- Initial source drawdown clock equals controlled ruin clock -/
theorem p2m810_initial_controlled_ruin_clock :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (x a : ℝ) (ω : Ω), 0 ≤ x → x ≤ a →
      (reflectedSupExit X.X x a ω : ℝ≥0∞) =
        ruinTime X (a-x) (barrierStrategy X (a-x) a) ω := by
  sorry
end Kyprianou.Ch08.StageB
