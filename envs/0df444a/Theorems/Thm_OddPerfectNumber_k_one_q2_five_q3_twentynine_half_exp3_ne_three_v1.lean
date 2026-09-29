-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp3_ne_three_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp3_ne_three_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T01:13:09.177003+00:00
-- url     : https://prove2.me/theorems/7617f22b-89b9-43dd-8f28-e879df3987c6
-- title:
--   q3=29 half-exponent a != 3
-- statement:
--   In canonical q3=29 coordinates with positive half-exponents, the 3-component half-exponent is not 3.
-- source:
--   Canonical q3=29 floor adapter. Half-exponent convention. Composes the accepted a=3 1093-role theorem with finite 1093-case elimination; no doubled floors assumed.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_half_exp3_ne_three_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h29mem : 29 ∈ (m ^ 2).primeFactors)
    (h29exp : (m ^ 2).factorization 29 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    a ≠ 3 := by sorry

end OddPerfectNumber
