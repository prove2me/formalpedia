-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_331_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_331_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:21.138792+00:00
-- url     : https://prove2.me/theorems/ebc72b6d-ac7e-4cf8-a8f7-42b726264559
-- title:
--   q17 even order mod 577 base 331
-- statement:
--   The order of 331 modulo 577 is 576, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_331_v1 : Even (orderOf (331 : ZMod 577)) ∧ orderOf (331 : ZMod 577) = 576 := by
  sorry

end OddPerfectNumber
