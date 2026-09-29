-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_half_exp5_ne_three_midq4_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp5_ne_three_midq4_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T12:26:15.442968+00:00
-- url     : https://prove2.me/theorems/d8c580d2-4150-4685-b5dc-4efa52ce9e47
-- title:
--   q13 b-half ne 3 for mid-size q4
-- statement:
--   If q4 < 19531 and p /= 19531, the 5-component half-exponent is not 3, since sigma(5^6) = 19531 is prime and outside the allowed support.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_half_exp5_ne_three_midq4_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4) (hq4lt : q4 < 19531)
    (hp19531 : p ≠ 19531)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h13mem : 13 ∈ (m ^ 2).primeFactors)
    (h13exp : (m ^ 2).factorization 13 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    b ≠ 3 := by
  sorry

end OddPerfectNumber
