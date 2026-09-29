-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_q4_31_e_two_canonical_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_q4_31_e_two_canonical_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T04:05:59.775524+00:00
-- url     : https://prove2.me/theorems/3d2da978-947f-46c6-b6e5-7c7d1c1aa9f0
-- title:
--   q3=29 q4=31 half-e=2 canonical contradiction
-- statement:
--   With q4=31 and half-exponent e=2, the five-term base-31 sum supplies prime 11 outside support; p=11 forces 6 | m^2 against Odd m.
-- source:
--   Canonical q3=29 keystone piece, half-exponent convention. Uses accepted 11-dvd arm and prime-restricted role; no floors assumed.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_q4_31_e_two_canonical_absurd_v1 (p m d q4 a b c e sigma : Nat)
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
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hq4eq : q4 = 31) (he2 : e = 2) :
    False := by sorry

end OddPerfectNumber
