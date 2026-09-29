-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_449_137_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_449_137_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:51:56.941338+00:00
-- url     : https://prove2.me/theorems/3bbafed8-c303-42f2-a337-3174a62535fe
-- title:
--   q17 even order mod 449 base 137
-- statement:
--   The order of 137 modulo 449 is 224, which is even.
-- source:
--   Even-order certificate for q17 D225 terminal (p=449).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_449_137_v1 : Even (orderOf (137 : ZMod 449)) ∧ orderOf (137 : ZMod 449) = 224 := by
  sorry

end OddPerfectNumber
