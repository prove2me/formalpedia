-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_role
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T21:59:32.487809+00:00
-- url     : https://prove2.me/theorems/451ed277-8e4e-4c2b-a212-c7a10f7ffce6
-- title:
--   The exponent-two 5-component forces Euler prime 31 or the fourth support prime
-- statement:
--   Under the q2=5, q3=19 four-support equations with q4>19, if the 5-component has exponent 2, the forced factor 31 of sigma(5^2) must be the Euler prime or the fourth support prime.
-- source:
--   The accepted local-to-global sigma lemma makes 31 divide the global divisor sum. The accepted finite-support restriction places 31 in {p,3,5,19,q4}; exact arithmetic removes 3,5,19, leaving p=31 or q4=31.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp5_two_role (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2) :
    p = 31 ∨ q4 = 31 := by sorry

end OddPerfectNumber
