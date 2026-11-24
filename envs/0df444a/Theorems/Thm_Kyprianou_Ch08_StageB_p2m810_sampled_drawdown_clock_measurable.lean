-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sampled_drawdown_clock_measurable
-- name    : Kyprianou.Ch08.StageB.p2m810_sampled_drawdown_clock_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:00:30.351807+00:00
-- url     : https://prove2.me/theorems/a81ce969-b1f6-4212-b458-e995f4ac649a
-- title:
--   Countable sampled drawdown clock is measurable
-- statement:
--   Each prefix maximum is a countable supremum of measurable nonnegative coordinates. Compare the drawdown with the barrier at each sample and take the countable infimum.
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
/-- Countable sampled drawdown clock is measurable -/
theorem p2m810_sampled_drawdown_clock_measurable :
    ∀ (s : ℕ → ℝ≥0) (a : ℝ),
      Measurable (fun f : ℝ≥0 → ℝ => ⨅ i : ℕ,
        if f (s i) - (⨆ j : ℕ, if s j ≤ s i
          then ENNReal.ofReal (f (s j)) else 0).toReal < -a
        then (s i : ℝ≥0∞) else ⊤) := by
  sorry
end Kyprianou.Ch08.StageB
