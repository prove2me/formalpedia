-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp5_eq_two_forces_q4_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp5_eq_two_forces_q4_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T23:58:55.186462+00:00
-- url     : https://prove2.me/theorems/a4c44ec0-cfe9-4d88-a322-23a0c7232950
-- title:
--   q3=29 half 5-exponent two forces q4 equals 71
-- statement:
--   If the half 5-exponent is two, sigma(5^4)=781=11*71 divides the divisor sum; the 11-arm forces p=11 and the 71-arm then leaves only q4=71.
-- source:
--   Canonical q3=29 reduced small-exponent result. S(5,4)=781=11*71; 11 forces p=11 (other roles impossible since q4>29); 71=p contradicts p=11, leaving q4=71. EXPONENT CONVENTION: b is a HALF exponent.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_half_exp5_eq_two_forces_q4_v1 (p m d q4 a b c e sigma : Nat)
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
    (hb2 : b = 2) :
    q4 = 71 := by sorry

end OddPerfectNumber
