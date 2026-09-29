-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd_q4gt71
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_four_absurd_q4gt71
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T22:10:03.607499+00:00
-- url     : https://prove2.me/theorems/d5d7a936-3f7c-4963-aecd-82989c85c9a0
-- title:
--   The exponent-four 5-component is impossible when the fourth support prime exceeds 71
-- statement:
--   The factor 11 of sigma(5^4) divides the global divisor sum. Finite support forces 11 to be p or q4 (the other support values are impossible); p=11 contradicts p ≡ 1 mod 4 and q4=11 contradicts q4>71.
-- source:
--   Use the accepted local-to-global sigma factor and finite-support restriction with r=11. Exact arithmetic eliminates support values 3, 5 and 19; the Euler congruence eliminates p=11 and q4>71 eliminates q4=11.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp5_four_absurd_q4gt71 (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 71 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 4) :
    False := by sorry

end OddPerfectNumber
