-- Prove2me | Theorems.Thm_Kyprianou_Ch04_eventBeforeClippedStopMeasurable
-- name    : Kyprianou.Ch04.eventBeforeClippedStopMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:58:34.788802+00:00
-- url     : https://prove2.me/theorems/f7881e23-eabb-4ab9-8eaf-905dc8e155f4
-- title:
--   eventBeforeClippedStopMeasurable
-- statement:
--   An event measurable at a deterministic time restricted to survival beyond that time is measurable at the clipped stopping time.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- The surviving portion of an event at a deterministic time is measurable at the clipped stop. -/
theorem Kyprianou.Ch04.eventBeforeClippedStopMeasurable {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (ht : IsStoppingTime F tau)
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[F s] A) :
    MeasurableSet[(ht.min_const s).measurableSpace]
      (A ∩ {w | tau w ≤ (s : WithTop NNReal)}ᶜ) := by
  sorry
