-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp5_ne_three_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp5_ne_three_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T15:34:00.034097+00:00
-- url     : https://prove2.me/theorems/d3bebaf4-04ca-443c-9c04-a3b34bb0eb11
-- title:
--   q17 half-exp 5 != 3 via 2 | sigma(5^6)
-- statement:
--   In the canonical q2=5,q3=17 branch, the 5-half-exponent cannot be 3 because sigma(5^6)=3906 is even while every support prime and the Euler prime are odd.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_half_exp5_ne_three_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 17 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 17 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h17mem : 17 ∈ (m ^ 2).primeFactors)
    (h17exp : (m ^ 2).factorization 17 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    b ≠ 3 := by
  sorry

end OddPerfectNumber
