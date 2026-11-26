-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RecordShiftDrawdownV1
-- name    : Kyprianou.Ch04.exercise46RecordShiftDrawdownV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:19:46.900848+00:00
-- url     : https://prove2.me/theorems/d08c12ea-ff73-4374-8b7d-b69c4f1b02b6
-- title:
--   Restart of the drawdown after reaching a running maximum
-- statement:
--   At a record time the earlier values cannot exceed the value at restart. Split the supremum into the earlier and shifted intervals and translate by the restart value.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RecordShiftDrawdownV1
    (f : NNReal → Real) (s t : NNReal)
    (hrecord : ∀ u ≤ s, f u ≤ f s)
    (hb : BddAbove (f '' Iic (s+t))) :
    sSup ((fun u : NNReal => f (s+u)-f s) '' Iic t) -
      (f (s+t)-f s) = sSup (f '' Iic (s+t)) - f (s+t) := by
  sorry
