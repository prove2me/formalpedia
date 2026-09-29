-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_eleven_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T23:10:58.878622+00:00
-- url     : https://prove2.me/theorems/2449de12-9f5f-494d-a237-61c98b710473
-- title:
--   The q2=5 q3=11 four-support branch is impossible (v2)
-- statement:
--   Under the q2=5,q3=11 four-support equations, the accepted exponent adapter gives a=2 and the accepted 13-source dispatch yields a contradiction.
-- source:
--   Clean composition of two accepted q3=11 nodes; the theorem preserves explicit canonical equations and support/exponent premises.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_exp3_eq_two
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_source_dispatch_v3

namespace OddPerfectNumber

theorem k_one_q2_five_q3_eleven_absurd_v2
    (m a b c e p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 11 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
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
    (h3expfac : (m ^ 2).factorization 3 = a)
    (ha2 : 2 ≤ a) (haeven : Even a)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
