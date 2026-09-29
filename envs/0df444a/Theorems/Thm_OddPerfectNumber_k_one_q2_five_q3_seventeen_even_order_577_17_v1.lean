-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_17_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_17_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:08.351557+00:00
-- url     : https://prove2.me/theorems/f9583b0f-36bd-4736-883e-15d938e8ac39
-- title:
--   q17 even order mod 577 base 17
-- statement:
--   The order of 17 modulo 577 is 288, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_17_v1 : Even (orderOf (17 : ZMod 577)) ∧ orderOf (17 : ZMod 577) = 288 := by
  sorry

end OddPerfectNumber
