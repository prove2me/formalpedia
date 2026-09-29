-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_D15_b_one_q4_le_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_b_one_q4_le_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T12:52:01.088571+00:00
-- url     : https://prove2.me/theorems/8f613a66-6552-4ae8-997b-1fca3d57bab1
-- title:
--   q31 D15 b=1 fourth-prime bound
-- statement:
--   With p = 29 and 5-component half-exponent exactly 1, upper abundance forces q4 <= 170.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirtyone_D15_b_one_q4_le_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hp29 : p = 29)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 31 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 31 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 31 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hb1 : b = 1) :
    q4 ≤ 170 := by
  sorry

end OddPerfectNumber
