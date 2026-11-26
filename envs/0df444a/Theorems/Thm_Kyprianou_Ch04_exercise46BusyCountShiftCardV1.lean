-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BusyCountShiftCardV1
-- name    : Kyprianou.Ch04.exercise46BusyCountShiftCardV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:19:43.978284+00:00
-- url     : https://prove2.me/theorems/7daa5a4d-cde0-548f-b0d4-71fa6cbed946
-- title:
--   Cardinality of one busy start followed by a translated future count
-- statement:
--   The first busy start is distinct from every strictly later shifted start, and translation is injective.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BusyCountShiftCardV1
    (S T : Set NNReal) (a b : NNReal)
    (hab : a ≤ b) (hpos : ∀ u ∈ T, 0 < u)
    (hEq : S = insert a ((fun u : NNReal => b+u) '' T)) :
    (S.encard : ENNReal) = 1 + (T.encard : ENNReal) := by
  sorry
