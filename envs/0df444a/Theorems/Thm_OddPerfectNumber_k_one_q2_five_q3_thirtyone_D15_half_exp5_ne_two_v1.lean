-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_D15_half_exp5_ne_two_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp5_ne_two_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T13:08:24.723638+00:00
-- url     : https://prove2.me/theorems/5337b4f0-c523-48a1-ae2e-6e3bd2bbe72f
-- title:
--   q31 D15 5-half-exp != 2
-- statement:
--   With p=29, half-exponent b=2 gives sigma(5^4)=781=11*71; 11 is outside support {3,5,31,q4} (q4>31) and != p.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirtyone_D15_half_exp5_ne_two_v1 (p m d q4 a b c e sigma : Nat)
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
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h31mem : 31 ∈ (m ^ 2).primeFactors)
    (h31exp : (m ^ 2).factorization 31 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    b ≠ 2 := by
  sorry

end OddPerfectNumber
