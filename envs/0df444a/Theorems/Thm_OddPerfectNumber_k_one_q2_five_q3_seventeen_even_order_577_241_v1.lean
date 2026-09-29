-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_241_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_241_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:16.73291+00:00
-- url     : https://prove2.me/theorems/cf7731e0-d382-46ee-a51a-4eb2af32654c
-- title:
--   q17 even order mod 577 base 241
-- statement:
--   The order of 241 modulo 577 is 192, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_241_v1 : Even (orderOf (241 : ZMod 577)) ∧ orderOf (241 : ZMod 577) = 192 := by
  sorry

end OddPerfectNumber
