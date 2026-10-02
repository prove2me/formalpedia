-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_source_dispatch_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_eleven_source_dispatch_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T22:45:47.029474+00:00
-- url     : https://prove2.me/theorems/578d7e7e-60c9-4d56-9592-138fca7175ed
-- title:
--   The 13-source dispatch for the q2=5 q3=11 branch (v2)
-- statement:
--   Once the 3-component has exponent two and the other local exponents are at least two, the forced 13 divisor of the global sigma is either the Euler prime or the fourth support prime; both cases contradict the canonical q2=5, q3=11 equations.
-- source:
--   Clean replacement for the first dispatch publication attempt; composes accepted local-sigma, support restriction, and q4=13 abundance nodes.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_q4_13_absurd_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_eleven_source_dispatch_v2
    (m b c e p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ 2 * 5 ^ b * 11 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 11 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
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
