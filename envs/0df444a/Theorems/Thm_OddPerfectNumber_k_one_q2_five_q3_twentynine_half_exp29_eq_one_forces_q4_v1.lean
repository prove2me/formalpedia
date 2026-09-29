-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp29_eq_one_forces_q4_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp29_eq_one_forces_q4_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T23:57:30.713111+00:00
-- url     : https://prove2.me/theorems/33c41255-94df-4c91-a7a9-a41b493212ab
-- title:
--   q3=29 half 29-exponent one forces q4 equals 67
-- statement:
--   If the half 29-exponent is one, sigma(29^2)=871=13*67 divides the divisor sum; 13 forces p=13 (then 7 divides m, impossible) and 67 forces p=67 (then 2 divides m, impossible) or q4=67.
-- source:
--   Canonical q3=29 reduced small-exponent result. S(29,2)=871=13*67; both prime factors feed the accepted restriction; the p=13 arm dies via 7 dividing m and the p=67 arm via 2 dividing m. EXPONENT CONVENTION: c is a HALF exponent.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_half_exp29_eq_one_forces_q4_v1 (p m d q4 a b c e sigma : Nat)
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
    (hc1 : c = 1) :
    q4 = 67 := by sorry

end OddPerfectNumber
