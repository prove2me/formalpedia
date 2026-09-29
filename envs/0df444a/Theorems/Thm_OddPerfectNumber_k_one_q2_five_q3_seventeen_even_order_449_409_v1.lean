-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_449_409_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_449_409_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:05.003524+00:00
-- url     : https://prove2.me/theorems/4dfe9353-c03b-4bf3-9fad-88aceda62a3c
-- title:
--   q17 even order mod 449 base 409
-- statement:
--   The order of 409 modulo 449 is 224, which is even.
-- source:
--   Even-order certificate for q17 D225 terminal (p=449).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_449_409_v1 : Even (orderOf (409 : ZMod 449)) ∧ orderOf (409 : ZMod 449) = 224 := by
  sorry

end OddPerfectNumber
