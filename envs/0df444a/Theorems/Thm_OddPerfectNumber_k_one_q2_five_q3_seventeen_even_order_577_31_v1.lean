-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_even_order_577_31_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_31_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:52:09.153337+00:00
-- url     : https://prove2.me/theorems/11d30cb8-6e17-478c-9043-a7435c3d92db
-- title:
--   q17 even order mod 577 base 31
-- statement:
--   The order of 31 modulo 577 is 18, which is even.
-- source:
--   Even-order certificate for q17 D289 terminal (p=577).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_even_order_577_31_v1 : Even (orderOf (31 : ZMod 577)) ∧ orderOf (31 : ZMod 577) = 18 := by
  sorry

end OddPerfectNumber
