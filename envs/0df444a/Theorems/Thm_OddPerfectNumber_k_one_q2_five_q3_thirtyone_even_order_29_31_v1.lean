-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_even_order_29_31_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirtyone_even_order_29_31_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T15:09:26.718009+00:00
-- url     : https://prove2.me/theorems/30c37175-80cd-4b1f-b7a9-23d42f703ab9
-- title:
--   q31 even order mod 29 for base 31
-- statement:
--   The multiplicative order of 31 modulo 29 is 28, which is even.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirtyone_even_order_29_31_v1 : Even (orderOf (31 : ZMod 29)) ∧ orderOf (31 : ZMod 29) = 28 := by
  sorry

end OddPerfectNumber
