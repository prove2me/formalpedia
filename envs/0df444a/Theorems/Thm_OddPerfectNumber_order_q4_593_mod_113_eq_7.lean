-- Prove2me | Theorems.Thm_OddPerfectNumber_order_q4_593_mod_113_eq_7
-- name    : OddPerfectNumber.order_q4_593_mod_113_eq_7
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T20:09:24.503962+00:00
-- url     : https://prove2.me/theorems/e70482ce-d9f8-44b9-ad10-6d65e4cd3f9b
-- title:
--   The q4=593 residue has order 7 modulo 113
-- statement:
--   The residue class of 593 modulo 113 has multiplicative order 7.
-- source:
--   Exact orderOf_eq_iff certificate with finite checks for the proper divisors below 7.

import Mathlib

namespace OddPerfectNumber

theorem order_q4_593_mod_113_eq_7 : orderOf (593 : ZMod 113) = 7 := by
  sorry

end OddPerfectNumber
