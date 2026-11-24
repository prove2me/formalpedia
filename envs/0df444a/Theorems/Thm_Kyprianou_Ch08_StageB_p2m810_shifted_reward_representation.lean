-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_shifted_reward_representation
-- name    : Kyprianou.Ch08.StageB.p2m810_shifted_reward_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:00:29.068701+00:00
-- url     : https://prove2.me/theorems/ae6f654e-cc2f-4c80-b41e-8257ae6f9c0b
-- title:
--   Borel future reward equals the true shifted record payoff
-- statement:
--   Use the proved exact shifted clock pair on the deterministic Cantor schedule; compose the measurable sampled clocks with the bounded discount function.
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
/-- Borel future reward equals the true shifted record payoff -/
theorem p2m810_shifted_reward_representation :
    ∀ (q a c : ℝ), 0 ≤ q →
      ∃ r : (ℝ≥0 → ℝ) → ℝ, Measurable r ∧
        (∀ f, 0 ≤ r f ∧ r f ≤ 1) ∧
        (∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
          (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F)
          (ω : Ω) (u : ℝ≥0),
          r (fun t => X.X (u+t) ω-X.X u ω) =
          (let f : ℝ≥0 → ℝ := fun t => X.X (u+t) ω-X.X u ω
      let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)
      let R : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // f t - sSup (f '' Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)
      if U < R then discountedAt q U else 0)) := by
  sorry
end Kyprianou.Ch08.StageB
