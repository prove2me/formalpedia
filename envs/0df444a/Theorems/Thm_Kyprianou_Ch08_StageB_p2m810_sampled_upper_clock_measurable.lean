-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sampled_upper_clock_measurable
-- name    : Kyprianou.Ch08.StageB.p2m810_sampled_upper_clock_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:00:25.727629+00:00
-- url     : https://prove2.me/theorems/1c6dcaba-1e98-4231-bbd0-f01167298f8c
-- title:
--   Countable sampled upper clock is measurable
-- statement:
--   Each sampled strict crossing is a measurable coordinate event, and the countable infimum is measurable.
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
/-- Countable sampled upper clock is measurable -/
theorem p2m810_sampled_upper_clock_measurable :
    ∀ (s : ℕ → ℝ≥0) (c : ℝ),
      Measurable (fun f : ℝ≥0 → ℝ =>
        ⨅ i : ℕ, if c < f (s i) then (s i : ℝ≥0∞) else ⊤) := by
  sorry
end Kyprianou.Ch08.StageB
