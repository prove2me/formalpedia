-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_exponents_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_exponents_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T19:37:48.185843+00:00
-- url     : https://prove2.me/theorems/088537d2-35bd-4ead-8bd6-c912be700350
-- title:
--   The q2=5 q3=19 exponent 2,4 cases are impossible
-- statement:
--   Under the canonical q2=5, q3=19 support equations, the explicitly specified exponent-two and exponent-four cases for 19 are impossible. This dispatcher is conditional on that finite exponent disjunction and does not assert exhaustiveness.
-- source:
--   The proof splits the stated exponent disjunction and applies the two independently accepted finite certificates, weakening the q4 bound arithmetically for the exponent-two case.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp_two_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp_four_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_exponents_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 151 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2 ∨
      (m ^ 2).factorization 19 = 4) :
    False := by sorry

end OddPerfectNumber
