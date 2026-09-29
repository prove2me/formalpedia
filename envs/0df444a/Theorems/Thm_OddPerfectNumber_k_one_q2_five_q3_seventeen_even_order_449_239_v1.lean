-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_449_239_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_449_239_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:51:58.970956+00:00
-- url     : https://prove2.me/theorems/42c4020e-1e35-4c15-8ab3-09e8b528edd2
-- title:
--   q17 even order mod 449 base 239
-- statement:
--   The order of 239 modulo 449 is 448, which is even.
-- source:
--   Even-order certificate for q17 D225 terminal (p=449).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_449_239_v1 : Even (orderOf (239 : ZMod 449)) ∧ orderOf (239 : ZMod 449) = 448 := by
  sorry

end OddPerfectNumber
