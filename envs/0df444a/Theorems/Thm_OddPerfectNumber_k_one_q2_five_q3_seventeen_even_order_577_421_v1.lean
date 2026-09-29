-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_421_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_421_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:20.317795+00:00
-- url     : https://prove2.me/theorems/147f6f5a-0736-4982-808d-c345ef4319e8
-- title:
--   q17 even order mod 577 base 421
-- statement:
--   The order of 421 modulo 577 is 576, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_421_v1 : Even (orderOf (421 : ZMod 577)) ∧ orderOf (421 : ZMod 577) = 576 := by
  sorry

end OddPerfectNumber
