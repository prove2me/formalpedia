-- Prove2me | Theorems.Thm_OddPerfectNumber_order_q4_587_mod_113_eq_56
-- name    : OddPerfectNumber.order_q4_587_mod_113_eq_56
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T20:24:45.101661+00:00
-- url     : https://prove2.me/theorems/5916abb0-a44d-4aed-a241-fa3e3fb7e415
-- title:
--   The q4=587 residue has order 56 modulo 113
-- statement:
--   The residue class of 587 modulo 113 has multiplicative order 56.
-- source:
--   Exact orderOf_eq_of_pow_and_pow_div_prime certificate using 56=2^3*7.

import Mathlib

namespace OddPerfectNumber

theorem order_q4_587_mod_113_eq_56 : orderOf (587 : ZMod 113) = 56 := by
  sorry

end OddPerfectNumber
