-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_filtered_restart_split
-- name    : Kyprianou.Ch08.StageB.p2m810_filtered_restart_split
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T08:00:38.148395+00:00
-- url     : https://prove2.me/theorems/b27b6da4-22df-4d1b-97f1-979e08c5488e
-- title:
--   Pathwise first-record payoff splitting at the initial maximum
-- statement:
--   Convert the initial drawdown clock to barrier controlled ruin for initial surplus a-x. Use barrierStrategy_upExit_before_controlledRuin_iff_rawExit and barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock. The next record clock is the first record plus the future upper clock. The future ruin clock is the first record plus the centred reflected bad clock. Multiply the discounts on the success event; on failure both payoffs vanish.
-- source:
--   Kyprianou (2006), Theorem 8.10(i), strong Markov record regeneration.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Pathwise first-record payoff splitting at the initial maximum -/
theorem p2m810_filtered_restart_split :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
      (X : SpectrallyNegativeLevy P F) (q x a l : ℝ),
      0 ≤ q → 0 < a → 0 < x → x ≤ a → x < l →
      ∀ (ω : Ω),
      let U := twoSidedExitUpTime X x ω
      let L := twoSidedExitDownTime X (x-a) ω
      let u := U.toNNReal
      let c := l-x
      let reward := (let f : ℝ≥0 → ℝ := fun t => X.X (u+t) ω-X.X u ω
      let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)
      let R : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // f t - sSup (f '' Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)
      if U < R then discountedAt q U else 0)
      (if tauPlus X.X l ω < reflectedSupExit X.X x a ω
        then discountedAt q (tauPlus X.X l ω) else 0) =
      (if U < L then Real.exp (-q*(u:ℝ)) * reward else 0) := by
  sorry
end Kyprianou.Ch08.StageB
