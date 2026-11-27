-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45SurvivalEventStopMeasurableV1
-- name    : Kyprianou.Ch04.exercise45SurvivalEventStopMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:36:11.422838+00:00
-- url     : https://prove2.me/theorems/dd7b0ea6-75fa-4f10-be63-07541822c637
-- title:
--   Survival event is measurable at a clipped stopping clock
-- statement:
--   An event measurable at time s intersected with survival beyond s is measurable at the clock min(i,τ) when i≥s.
-- source:
--   Kyprianou Exercise 4.5

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45SurvivalEventStopMeasurableV1 {Ω : Type} [MeasurableSpace Ω] (F : Filtration NNReal inferInstance)
    (τ : Ω → NNReal) (ht : IsStoppingTime F (fun w => (τ w : WithTop NNReal)))
    (s i : NNReal) (hi : s ≤ i) (A : Set Ω) (hA : MeasurableSet[F s] A)
    (hstop : IsStoppingTime F (fun w => (↑(min i (τ w)) : WithTop NNReal))) :
    MeasurableSet[hstop.measurableSpace] (A ∩ {w | s < τ w}) := by
  sorry
end Kyprianou.Ch04
