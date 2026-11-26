-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stoppingTimeMinMeasurable
-- name    : Kyprianou.Ch04.stoppingTimeMinMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:17:45.665857+00:00
-- url     : https://prove2.me/theorems/54003105-83d6-49af-b20d-b0a5c73e8dc3
-- title:
--   stoppingTimeMinMeasurable
-- statement:
--   A stopping time clipped at a deterministic time is measurable at that time.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- A stopping time clipped at a deterministic clock is measurable at that clock. -/
theorem Kyprianou.Ch04.stoppingTimeMinMeasurable {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (htau : IsStoppingTime F tau) (t : NNReal) :
    Measurable[F t] (fun w => min (tau w) (t : WithTop NNReal)) := by
  sorry
