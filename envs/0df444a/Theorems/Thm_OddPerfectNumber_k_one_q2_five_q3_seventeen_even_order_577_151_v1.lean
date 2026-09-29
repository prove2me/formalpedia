-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_151_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_151_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:10.891957+00:00
-- url     : https://prove2.me/theorems/bed2628c-882e-4e03-a9ee-5af7559bfc6d
-- title:
--   q17 even order mod 577 base 151
-- statement:
--   The order of 151 modulo 577 is 144, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_151_v1 : Even (orderOf (151 : ZMod 577)) ∧ orderOf (151 : ZMod 577) = 144 := by
  sorry

end OddPerfectNumber
