-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_even_order_29_5_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirtyone_even_order_29_5_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T15:09:25.761716+00:00
-- url     : https://prove2.me/theorems/3c72a313-72af-44f5-8e6d-3e816d633d44
-- title:
--   q31 even order mod 29 for base 5
-- statement:
--   The multiplicative order of 5 modulo 29 is 14, which is even.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirtyone_even_order_29_5_v1 : Even (orderOf (5 : ZMod 29)) ∧ orderOf (5 : ZMod 29) = 14 := by
  sorry

end OddPerfectNumber
