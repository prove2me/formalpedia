-- Prove2me | Theorems.Thm_OddPerfectNumber_order_three_mod_593_eq_592
-- name    : OddPerfectNumber.order_three_mod_593_eq_592
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T15:59:23.327983+00:00
-- url     : https://prove2.me/theorems/285ad75e-8c07-4dd1-8d04-46cfae4fbf30
-- title:
--   The order of 3 modulo 593 is 592
-- statement:
--   The residue class of 3 modulo 593 has multiplicative order 592.
-- source:
--   Exact finite order certificate for the D=57 q4=593 candidate, using orderOf_eq_iff and exact ZMod arithmetic.

import Mathlib

namespace OddPerfectNumber

theorem order_three_mod_593_eq_592 :
    orderOf (3 : ZMod 593) = 592 := by
  sorry

end OddPerfectNumber
