-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_449_443_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_449_443_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:07.408621+00:00
-- url     : https://prove2.me/theorems/f823ac09-fb29-4599-85d2-b5b80bf3a531
-- title:
--   q17 even order mod 449 base 443
-- statement:
--   The order of 443 modulo 449 is 448, which is even.
-- source:
--   Even-order certificate for q17 D225 terminal (p=449).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_449_443_v1 : Even (orderOf (443 : ZMod 449)) ∧ orderOf (443 : ZMod 449) = 448 := by
  sorry

end OddPerfectNumber
