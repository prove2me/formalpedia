-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_even_order_29_3_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirtyone_even_order_29_3_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T15:09:25.360596+00:00
-- url     : https://prove2.me/theorems/0c32fe13-e0ce-4516-8a6f-b598e2a4282b
-- title:
--   q31 even order mod 29 for base 3
-- statement:
--   The multiplicative order of 3 modulo 29 is 28, which is even.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirtyone_even_order_29_3_v1 : Even (orderOf (3 : ZMod 29)) ∧ orderOf (3 : ZMod 29) = 28 := by
  sorry

end OddPerfectNumber
