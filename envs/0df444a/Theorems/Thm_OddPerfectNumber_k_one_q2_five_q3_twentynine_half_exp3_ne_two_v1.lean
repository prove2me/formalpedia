-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp3_ne_two_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp3_ne_two_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T23:51:17.967498+00:00
-- url     : https://prove2.me/theorems/e5319097-b2c3-41ef-8c07-520b876c52ba
-- title:
--   The q3=29 half exponent of 3 is not two
-- statement:
--   In the canonical q3=29 four-support coordinates with positive half exponents, the half exponent of 3 is not two: sigma(3^4)=121 forces 11 to divide the divisor sum, the support restriction forces p=11, and then 2 divides m, contradicting oddness.
-- source:
--   Canonical q3=29 small-exponent exclusion. S(3,4)=121 gives 11 dividing the global divisor sum; accepted restriction forces p=11; then (p+1)/2=6 divides m^2 so 2 divides m, against Odd m. EXPONENT CONVENTION: a is a HALF exponent.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_half_exp3_ne_two_v1 (p m d q4 a b c e sigma : Nat)
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
    a ≠ 2 := by sorry

end OddPerfectNumber
