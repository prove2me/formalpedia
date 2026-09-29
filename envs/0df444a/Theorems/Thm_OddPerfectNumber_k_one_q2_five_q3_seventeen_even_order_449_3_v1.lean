-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_449_3_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_449_3_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:51:53.018878+00:00
-- url     : https://prove2.me/theorems/66753375-0e63-4e8f-85aa-5f6d062e9dee
-- title:
--   q17 even order mod 449 base 3
-- statement:
--   The order of 3 modulo 449 is 448, which is even.
-- source:
--   Even-order certificate for q17 D225 terminal (p=449).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_449_3_v1 : Even (orderOf (3 : ZMod 449)) ∧ orderOf (3 : ZMod 449) = 448 := by
  sorry

end OddPerfectNumber
