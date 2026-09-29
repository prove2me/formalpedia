-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_449_17_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_449_17_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:51:56.682656+00:00
-- url     : https://prove2.me/theorems/9c14469b-be3c-4593-9294-dec0c932b94f
-- title:
--   q17 even order mod 449 base 17
-- statement:
--   The order of 17 modulo 449 is 448, which is even.
-- source:
--   Even-order certificate for q17 D225 terminal (p=449).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_449_17_v1 : Even (orderOf (17 : ZMod 449)) ∧ orderOf (17 : ZMod 449) = 448 := by
  sorry

end OddPerfectNumber
