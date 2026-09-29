-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b1_q31_e1_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_b1_q31_e1_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:19:33.801312+00:00
-- url     : https://prove2.me/theorems/b3e65b34-7cf0-4e44-85bb-da0217ba11cc
-- title:
--   q3=29 b=1 q4=31 e=1 terminal contradiction
-- statement:
--   With half exponents b=1, q4=31, e=1, the q4-local sigma sum S(31,2)=993=3*331 forces the prime 331 into the divisor sum, which is neither the Euler prime nor any support prime.
-- source:
--   Canonical q3=29 floor terminal. S(31,2)=993=3*331; 331 is prime, 331%4=3 so 331=p forces 2|m against Odd m; 331 cannot be 3,5,29,31. EXPONENT CONVENTION: b,e are HALF exponents.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_b1_q31_e1_absurd_v1 (p m d q4 a b c e sigma : Nat)
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
    (hq4mem : q4 ∈ (m ^ 2).primeFactors)
    (hq4exp : (m ^ 2).factorization q4 = 2*e)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hb1 : b = 1) (hq4eq : q4 = 31) (he1 : e = 1) :
    False := by sorry

end OddPerfectNumber
