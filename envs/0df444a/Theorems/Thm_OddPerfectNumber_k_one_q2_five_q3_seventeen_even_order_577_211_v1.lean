-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_211_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_211_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:15.545259+00:00
-- url     : https://prove2.me/theorems/64cb587d-8a1e-4e2f-9177-1cf8c62b44ce
-- title:
--   q17 even order mod 577 base 211
-- statement:
--   The order of 211 modulo 577 is 576, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_211_v1 : Even (orderOf (211 : ZMod 577)) ∧ orderOf (211 : ZMod 577) = 576 := by
  sorry

end OddPerfectNumber
