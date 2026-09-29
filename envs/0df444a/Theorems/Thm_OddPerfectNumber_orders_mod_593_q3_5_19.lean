-- Prove2me | Theorems.Thm_OddPerfectNumber_orders_mod_593_q3_5_19
-- name    : OddPerfectNumber.orders_mod_593_q3_5_19
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T20:15:40.736124+00:00
-- url     : https://prove2.me/theorems/4680b047-5c51-497e-9873-7e349ddea148
-- title:
--   Orders of 5 and 19 modulo 593
-- statement:
--   The exact multiplicative orders of 5 and 19 modulo 593 are 592 and 148 respectively.
-- source:
--   Exact orderOf_eq_of_pow_and_pow_div_prime certificates with the 592=2^4*37 and 148=2^2*37 factorizations.

import Mathlib

namespace OddPerfectNumber

theorem orders_mod_593_q3_5_19 :
    orderOf (5 : ZMod 593) = 592 ∧
      orderOf (19 : ZMod 593) = 148 := by
  sorry

end OddPerfectNumber
