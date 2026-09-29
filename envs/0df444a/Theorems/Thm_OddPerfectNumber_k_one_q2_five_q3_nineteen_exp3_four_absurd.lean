-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_four_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_four_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T21:13:34.337866+00:00
-- url     : https://prove2.me/theorems/24c19ee8-c5cd-4dc3-b9d3-0a92ee33a2ec
-- title:
--   The q2=5 q3=19 exponent-four 3-component subcase is impossible
-- statement:
--   Under the canonical q2=5, q3=19 support equations, the exact exponent-four case for the 3-component is impossible because sigma(3^4)=121 is divisible by the external prime 11.
-- source:
--   The accepted local sigma-factor divisibility theorem turns the factor 11 of sigma(3^4) into a divisor of the global square-part sigma; the accepted finite-support restriction excludes 11 from support {3,5,19,q4} when q4>19.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp3_four_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 4) :
    False := by sorry

end OddPerfectNumber
