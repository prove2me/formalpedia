-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_absurd_q4gt31
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_absurd_q4gt31
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T22:16:07.660425+00:00
-- url     : https://prove2.me/theorems/b46809c2-e55d-4824-81c6-df7102d1e21d
-- title:
--   The exponent-two 5-component is impossible when the fourth support prime exceeds 31
-- statement:
--   The accepted 5^2 source-role lemma gives p=31 or q4=31. The Euler congruence rules out p=31, while q4>31 rules out q4=31.
-- source:
--   Apply the accepted role theorem. In the p=31 case, 31 mod 4 is 3, contradicting p mod 4 = 1. In the q4=31 case, q4>31 is impossible.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp5_two_absurd_q4gt31 (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2) :
    False := by sorry

end OddPerfectNumber
