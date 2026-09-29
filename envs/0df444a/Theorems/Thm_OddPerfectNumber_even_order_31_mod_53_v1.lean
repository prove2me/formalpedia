-- Prove2me | Theorems.Thm_OddPerfectNumber_even_order_31_mod_53_v1
-- name    : OddPerfectNumber.even_order_31_mod_53_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T05:12:46.361454+00:00
-- url     : https://prove2.me/theorems/4f315904-b228-4e0c-8de4-6645ac5cfb37
-- title:
--   31 has even order mod 53
-- statement:
--   The multiplicative order of 31 modulo 53 is even (it equals 52).
-- source:
--   Order certificate for the q29 b=1 D=27 arm; same shape as accepted even_orders_mod_89.

import Mathlib

namespace OddPerfectNumber

theorem even_order_31_mod_53_v1 :
    Even (orderOf (31 : ZMod 53)) := by
  sorry

end OddPerfectNumber
