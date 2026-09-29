-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_source_dispatch_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_eleven_source_dispatch_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T22:57:21.797538+00:00
-- url     : https://prove2.me/theorems/5179cca4-0159-4b4e-8655-361ab01acac6
-- title:
--   The 13-source dispatch for the q2=5 q3=11 branch (v3)
-- statement:
--   Once the 3-component has exponent two and the other local exponents are at least two, the forced 13 divisor of the global sigma is either the Euler prime or the fourth support prime; both cases contradict the canonical q2=5, q3=11 equations.
-- source:
--   Clean replacement after the source-dispatch proof exposed the missing abundance-upper binder needed by the q4=13 child.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_q4_13_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_half_successor_support

namespace OddPerfectNumber

theorem k_one_q2_five_q3_eleven_source_dispatch_v3
    (m b c e p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ 2 * 5 ^ b * 11 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 11 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hupper : sigma ≤ 2 * m ^ 2)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 11 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 11 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
