-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_271_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_271_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:17.101544+00:00
-- url     : https://prove2.me/theorems/2f6588d6-a924-4448-85c2-1a618b7e4f14
-- title:
--   q17 even order mod 577 base 271
-- statement:
--   The order of 271 modulo 577 is 288, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_271_v1 : Even (orderOf (271 : ZMod 577)) ∧ orderOf (271 : ZMod 577) = 288 := by
  sorry

end OddPerfectNumber
