-- Prove2me | Theorems.Thm_OddPerfectNumber_even_order_three_mod_113
-- name    : OddPerfectNumber.even_order_three_mod_113
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T12:33:43.839083+00:00
-- url     : https://prove2.me/theorems/6621ecc3-636a-4f4a-99f2-d73ee0b9f2a4
-- title:
--   Even multiplicative order of 3 modulo 113
-- statement:
--   The residue class of 3 modulo 113 has even multiplicative order. The order divides 112 = 16 * 7, and neither 1 nor 7 is the order since 3 != 1 and 3^7 != 1 mod 113.
-- source:
--   Even-order certificate for the D=57 (p=113) small-D elimination: orderOf divides 112 by Fermat (decide), odd divisors {1,7} excluded by decide, so the order is even and 113 cannot divide the odd-length geometric sums at bases 3, 5, 19 via geom_sum_not_dvd_of_even_order.

import Mathlib

namespace OddPerfectNumber

theorem even_order_three_mod_113 :
    Even (orderOf (3 : ZMod 113)) := by
  sorry

end OddPerfectNumber
