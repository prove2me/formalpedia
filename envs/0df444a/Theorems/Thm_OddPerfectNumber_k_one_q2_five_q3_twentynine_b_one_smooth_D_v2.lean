-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_smooth_D_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_smooth_D_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T07:00:11.409805+00:00
-- url     : https://prove2.me/theorems/29a14657-7b99-4644-bac4-671d214f3ff5
-- title:
--   b=1 smoothness v2 with positivity premise
-- statement:
--   With 0<m, every prime divisor of D is among 3,5,29,31 with bounded exponents, so D divides 1820475.
-- source:
--   opn-q29-b1-smooth-v2

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_b_one_smooth_D_v2 (D m q4 : Nat)
    (hlt : D < 107) (hDpos : 0 < D) (hmpos : 0 < m) (hDm : D ∣ m ^ 2)
    (hsup : ∀ x ∈ (m ^ 2).primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4 : q4 = 31) :
    D ∣ 1820475 := by
  sorry

end OddPerfectNumber
