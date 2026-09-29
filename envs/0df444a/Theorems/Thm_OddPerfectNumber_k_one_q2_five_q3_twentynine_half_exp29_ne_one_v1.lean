-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp29_ne_one_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp29_ne_one_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:04:40.143858+00:00
-- url     : https://prove2.me/theorems/07d8a199-d2f3-45d1-b4e2-c14c82886883
-- title:
--   The q3=29 half exponent of 29 is not one
-- statement:
--   The half 29-exponent is not one: sigma(29^2)=871 gives 13 dividing the divisor sum, forcing p=13, and then 7 divides m, outside the support.
-- source:
--   Canonical q3=29 small-exponent exclusion. S(29,2)=871=13*67; 13 forces p=13 (13 cannot be 3,5,29 or q4>29); then (p+1)/2=7 divides m^2 hence m, contradicting support. EXPONENT CONVENTION: c is a HALF exponent.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_half_exp29_ne_one_v1 (p m d q4 a b c e sigma : Nat)
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
    c ≠ 1 := by sorry

end OddPerfectNumber
