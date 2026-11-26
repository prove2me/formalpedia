-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46PredictableBeforeClockV1
-- name    : Kyprianou.Ch04.exercise46PredictableBeforeClockV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:36:37.390799+00:00
-- url     : https://prove2.me/theorems/c2b732fd-1119-4a46-bfa5-8bf48f7fa6a4
-- title:
--   Inclusive time before an extended stopping clock is predictable
-- statement:
--   The strict post-stop event is a countable union of predictable rectangles over a countable dense time set. Take its complement.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46PredictableBeforeClockV1
    {Omega : Type} [MeasurableSpace Omega]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G A) :
    MeasurableSet[G.predictable] {p : NNReal × Omega | (p.1 : WithTop NNReal) ≤ A p.2} := by
  sorry
