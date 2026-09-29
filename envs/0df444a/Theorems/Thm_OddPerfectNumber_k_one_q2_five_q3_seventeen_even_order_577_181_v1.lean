-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_181_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_181_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:13.057043+00:00
-- url     : https://prove2.me/theorems/ad663080-88a0-4ef9-82a4-99aa5a8ee501
-- title:
--   q17 even order mod 577 base 181
-- statement:
--   The order of 181 modulo 577 is 288, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_181_v1 : Even (orderOf (181 : ZMod 577)) ∧ orderOf (181 : ZMod 577) = 288 := by
  sorry

end OddPerfectNumber
