-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_filtered_fresh_reward
-- name    : Kyprianou.Ch08.StageB.p2m810_filtered_fresh_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:00:46.491773+00:00
-- url     : https://prove2.me/theorems/4e8d60ea-35a8-476d-8157-9494aa4227c4
-- title:
--   Fresh all-time record payoff agrees with the source strict payoff
-- statement:
--   At shift zero, the centred process is the original process. Use the proved positive open clock equality and exact original running-supremum bridge; the initial zero time is outside both strict crossing sets.
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
/-- Fresh all-time record payoff agrees with the source strict payoff -/
theorem p2m810_filtered_fresh_reward :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
      (X : SpectrallyNegativeLevy P F) (q a c : ℝ),
      0 < a → 0 < c →
      ∀ (ω : Ω),
      let u : ℝ≥0 := 0
      (let f : ℝ≥0 → ℝ := fun t => X.X (u+t) ω-X.X u ω
      let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)
      let R : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // f t - sSup (f '' Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)
      if U < R then discountedAt q U else 0) =
      (if tauPlus X.X c ω < reflectedSupExit X.X 0 a ω
        then discountedAt q (tauPlus X.X c ω) else 0) := by
  sorry
end Kyprianou.Ch08.StageB
