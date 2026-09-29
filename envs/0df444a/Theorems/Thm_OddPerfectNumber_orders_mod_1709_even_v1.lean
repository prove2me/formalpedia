-- Prove2me | Theorems.Thm_OddPerfectNumber_orders_mod_1709_even_v1
-- name    : OddPerfectNumber.orders_mod_1709_even_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T03:37:49.024363+00:00
-- url     : https://prove2.me/theorems/913c03df-f611-4b7b-a67c-f1fe8449204e
-- title:
--   The four q3=19 large-D orders modulo 1709 are even
-- statement:
--   Modulo 1709, the multiplicative orders of 3, 5, 19, and 101 are all even; the proof uses 1708=4*427 and the exact non-unit odd-part powers 390, 1708, 390, and 1319.
-- source:
--   Exact finite-field order certificate for the q3=19 large-D source obstruction.

import Mathlib

namespace OddPerfectNumber

theorem orders_mod_1709_even_v1 :
    Even (orderOf (3 : ZMod 1709)) ∧
    Even (orderOf (5 : ZMod 1709)) ∧
    Even (orderOf (19 : ZMod 1709)) ∧
    Even (orderOf (101 : ZMod 1709)) := by
  sorry

end OddPerfectNumber
