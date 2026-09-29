-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_5_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_5_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:10.571667+00:00
-- url     : https://prove2.me/theorems/4b457612-a1b7-4348-ac51-96a456dda7af
-- title:
--   q17 even order mod 577 base 5
-- statement:
--   The order of 5 modulo 577 is 576, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_5_v1 : Even (orderOf (5 : ZMod 577)) ∧ orderOf (5 : ZMod 577) = 576 := by
  sorry

end OddPerfectNumber
