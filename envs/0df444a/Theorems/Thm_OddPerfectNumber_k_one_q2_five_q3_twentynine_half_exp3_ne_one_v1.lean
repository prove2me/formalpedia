-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp3_ne_one_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp3_ne_one_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T23:46:26.899844+00:00
-- url     : https://prove2.me/theorems/f59626fc-bae9-43fa-8996-d42ed8812b89
-- title:
--   The q3=29 half exponent of 3 is not one
-- statement:
--   In the canonical q3=29 four-support coordinates with positive half exponents, the half exponent of 3 is not one: sigma(3^2)=13 is external to {3,5,29,q4} with q4>29, forcing p=13, and then 7 divides m^2 hence m, contradicting the support.
-- source:
--   Canonical q3=29 small-exponent exclusion. Uses the accepted local-sigma-divides-global theorem at 3, evaluates S(3,2)=13, applies the accepted four-support sigma-prime restriction, and closes the forced p=13 case via 7 dividing m. EXPONENT CONVENTION: a is a HALF exponent.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_half_exp3_ne_one_v1 (p m d q4 a b c e sigma : Nat)
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
    a ≠ 1 := by sorry

end OddPerfectNumber
