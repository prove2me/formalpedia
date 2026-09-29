-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_449_307_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_449_307_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:01.893201+00:00
-- url     : https://prove2.me/theorems/b190dc62-6e1e-480b-a396-e89766922910
-- title:
--   q17 even order mod 449 base 307
-- statement:
--   The order of 307 modulo 449 is 448, which is even.
-- source:
--   Even-order certificate for q17 D225 terminal (p=449).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_449_307_v1 : Even (orderOf (307 : ZMod 449)) ∧ orderOf (307 : ZMod 449) = 448 := by
  sorry

end OddPerfectNumber
