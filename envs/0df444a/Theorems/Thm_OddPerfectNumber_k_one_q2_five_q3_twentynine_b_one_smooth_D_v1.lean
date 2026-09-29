-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_smooth_D_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_smooth_D_v1
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-18T06:49:51.6034+00:00
-- url     : https://prove2.me/theorems/b763f170-4cfa-477a-9d78-0540dac58854
-- title:
--   q3=29 b=1 smoothness bound
-- statement:
--   Below 107, a divisor of m^2 supported on {3,5,29,31} divides 1820475.
-- source:
--   Valuation caps from D<107 plus support restriction; feeds the b=1 D-enumeration.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_b_one_smooth_D_v1 (D m q4 : Nat)
    (hlt : D < 107) (hDpos : 0 < D) (hDm : D ∣ m ^ 2)
    (hsup : ∀ x ∈ (m ^ 2).primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4 : q4 = 31) :
    D ∣ 1820475 := by
  sorry

end OddPerfectNumber
