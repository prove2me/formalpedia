-- Prove2me | Theorems.Thm_OddPerfectNumber_even_orders_mod_61_q3_twentynine
-- name    : OddPerfectNumber.even_orders_mod_61_q3_twentynine
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T06:27:43.606212+00:00
-- url     : https://prove2.me/theorems/cae5dfdd-1b43-48ad-b77d-e81db7fff93a
-- title:
--   Even orders of 3, 5, and 29 modulo 61
-- statement:
--   The fixed q3=29 support bases 3, 5, and 29 all have even multiplicative order modulo the Euler prime 61.
-- source:
--   Odd-part certificate: 61−1=4·15; explicit fifteenth-power residues rule out odd order for each fixed base.

import Mathlib

namespace OddPerfectNumber

theorem even_orders_mod_61_q3_twentynine :
    Even (orderOf (3 : ZMod 61)) ∧
      Even (orderOf (5 : ZMod 61)) ∧
      Even (orderOf (29 : ZMod 61)) := by
  sorry

end OddPerfectNumber
