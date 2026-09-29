-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_3_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_3_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:06.016178+00:00
-- url     : https://prove2.me/theorems/174e17e9-8f05-45d9-a042-ac4a6eb82a82
-- title:
--   q17 even order mod 577 base 3
-- statement:
--   The order of 3 modulo 577 is 48, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_3_v1 : Even (orderOf (3 : ZMod 577)) ∧ orderOf (3 : ZMod 577) = 48 := by
  sorry

end OddPerfectNumber
