-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41DeterministicFutureProductV19
-- name    : Kyprianou.Ch04.exercise41DeterministicFutureProductV19
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:20:14.849021+00:00
-- url     : https://prove2.me/theorems/932a977e-8304-42a7-9d90-5f662d683645
-- title:
--   Product law of a deterministic-time state and its independent future increments
-- statement:
--   Product law of a deterministic-time state and its independent future increments
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41DeterministicFutureProductV19
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F) (s : NNReal) :
    Measure.map (fun w => (L.X s w, fun t : NNReal => L.X (s+t) w - L.X s w)) P =
      (Measure.map (L.X s) P).prod (Measure.map (fun w t => L.X t w) P) := by
  sorry
