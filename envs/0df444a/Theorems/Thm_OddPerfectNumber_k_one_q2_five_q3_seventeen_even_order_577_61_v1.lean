-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_61_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_61_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:08.733748+00:00
-- url     : https://prove2.me/theorems/a2c2045d-4bdc-4484-843d-e3f7349a5b43
-- title:
--   q17 even order mod 577 base 61
-- statement:
--   The order of 61 modulo 577 is 576, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_61_v1 : Even (orderOf (61 : ZMod 577)) ∧ orderOf (61 : ZMod 577) = 576 := by
  sorry

end OddPerfectNumber
