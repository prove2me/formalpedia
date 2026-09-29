-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_two_role
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_two_role
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T21:51:12.152242+00:00
-- url     : https://prove2.me/theorems/4386edc8-9cd9-408c-b806-6f820fa073c6
-- title:
--   The exponent-two 3-component forces Euler prime 13
-- statement:
--   Under the q2=5, q3=19 four-support equations with q4>19, if the 3-component has exponent 2, then the forced factor 13 of sigma(3^2) must be the Euler prime p.
-- source:
--   The accepted local-to-global sigma lemma makes 13 divide the global divisor sum. The accepted finite-support restriction places 13 in {p,3,5,19,q4}; exact arithmetic and q4>19 leave only p=13.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp3_two_role (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2) :
    p = 13 := by sorry

end OddPerfectNumber
