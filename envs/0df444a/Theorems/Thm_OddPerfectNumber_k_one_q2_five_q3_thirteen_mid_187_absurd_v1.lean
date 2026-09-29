-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_187_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_187_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:23:01.381962+00:00
-- url     : https://prove2.me/theorems/97b2c7d5-5ff4-499f-8fa6-14d0924f7e53
-- title:
--   q3=13 middle candidate D=187 impossible by support
-- statement:
--   The middle-range candidate D=187 with q4=17 is impossible: 11 divides 187 hence m, but 11 is outside the support {3,5,13,17}.
-- source:
--   Canonical q3=13 middle-candidate elimination. D=187=11*17; 11|D|m^2 gives 11|m, outside support. Shortest of the 13 kills.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_mid_187_absurd_v1 (m D q4 : Nat)
    (hm : Odd m)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hDm : D ∣ m ^ 2)
    (hD : D = 187) (hq4 : q4 = 17) :
    False := by sorry

end OddPerfectNumber
