-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_shifted_controlled_bad_clock
-- name    : Kyprianou.Ch08.StageB.p2m810_shifted_controlled_bad_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:15:48.649884+00:00
-- url     : https://prove2.me/theorems/83185cdb-3294-4861-a8f2-fcac700329a5
-- title:
--   Shifted controlled bad clock equals centred drawdown clock
-- statement:
--   Use the proved shift of compact running suprema. The centred path starts at zero and its running supremum is nonnegative. Hence max 0 may be removed and the two infima have the same crossing predicates.
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
/-- Shifted controlled bad clock equals centred drawdown clock -/
theorem p2m810_shifted_controlled_bad_clock :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (a : ℝ) (ω : Ω) (u : ℝ≥0),
      (⨅ (t : ℝ≥0) (_ : a + (X.X (u+t) ω - X.X u ω) <
        max 0 (sSup ((fun r : ℝ≥0 => X.X (u+r) ω) '' Icc 0 t) - X.X u ω)),
        (t : ℝ≥0∞)) =
      (⨅ i : {t : ℝ≥0 // X.X (u+t) ω-X.X u ω -
        sSup ((fun r : ℝ≥0 => X.X (u+r) ω-X.X u ω) '' Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)) := by
  sorry
end Kyprianou.Ch08.StageB
