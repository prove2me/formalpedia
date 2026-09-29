-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_449_5_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_449_5_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:51:55.98659+00:00
-- url     : https://prove2.me/theorems/2b9d10d9-16dc-4795-bb7f-eed6e43bcfc4
-- title:
--   q17 even order mod 449 base 5
-- statement:
--   The order of 5 modulo 449 is 14, which is even.
-- source:
--   Even-order certificate for q17 D225 terminal (p=449).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_449_5_v1 : Even (orderOf (5 : ZMod 449)) ∧ orderOf (5 : ZMod 449) = 14 := by
  sorry

end OddPerfectNumber
