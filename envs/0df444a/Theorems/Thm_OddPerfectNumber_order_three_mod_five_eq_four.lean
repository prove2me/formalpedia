-- Prove2me | Theorems.Thm_OddPerfectNumber_order_three_mod_five_eq_four
-- name    : OddPerfectNumber.order_three_mod_five_eq_four
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T00:27:34.557444+00:00
-- url     : https://prove2.me/theorems/f1e7ec1c-8217-471f-b116-30ab01a1ec4e
-- title:
--   The order of 3 modulo 5 is four
-- statement:
--   The residue class of 3 modulo 5 has multiplicative order 4.
-- source:
--   Finite order certificate by orderOf_eq_iff and exact ZMod arithmetic.

import Mathlib

namespace OddPerfectNumber

theorem order_three_mod_five_eq_four :
    orderOf (3 : ZMod 5) = 4 := by
  sorry

end OddPerfectNumber
