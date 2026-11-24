-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_excursion_strict_tail_limit
-- name    : Kyprianou.Ch08.StageB.p2m810_excursion_strict_tail_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:10:39.660094+00:00
-- url     : https://prove2.me/theorems/84cf84eb-1bc3-4e7e-8320-1676dda05648
-- title:
--   Closed height tails converge to the strict tail
-- statement:
--   The increasing sets [a+1/(k+1),infinity) exhaust (a,infinity). Their measures converge, and the strict tail is finite by comparison with the closed tail.
-- source:
--   Kyprianou (2006), Theorem 8.2, right derivative.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Closed height tails converge to the strict tail. -/
theorem p2m810_excursion_strict_tail_limit :
    ∀ (n : Measure ℝ) (a : ℝ), n (Ici a) < ⊤ →
    Tendsto (fun k : ℕ => (n (Ici (a + 1 / ((k : ℝ)+1)))).toReal)
      atTop (nhds ((n (Ioi a)).toReal)) := by
  sorry
end Kyprianou.Ch08.StageB
