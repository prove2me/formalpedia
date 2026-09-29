-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_even_order_29_331_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirtyone_even_order_29_331_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T15:09:24.939669+00:00
-- url     : https://prove2.me/theorems/6b53a6dd-aceb-450c-99ca-1f27ac52a935
-- title:
--   q31 even order mod 29 for base 331
-- statement:
--   The multiplicative order of 331 modulo 29 is 4, which is even.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirtyone_even_order_29_331_v1 : Even (orderOf (331 : ZMod 29)) ∧ orderOf (331 : ZMod 29) = 4 := by
  sorry

end OddPerfectNumber
