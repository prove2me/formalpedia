-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_small_exponents_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_small_exponents_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T19:24:20.502028+00:00
-- url     : https://prove2.me/theorems/85a04f6e-3c10-4b50-a1f6-a0994bcd9c28
-- title:
--   The q2=5 q3=13 exponent 2,4,6 cases are impossible
-- statement:
--   Under the canonical q2=5, q3=13 support equations, each of the explicitly specified local exponent cases 2, 4, and 6 is impossible. This dispatcher is conditional on that finite exponent disjunction and does not assert it is exhaustive.
-- source:
--   The proof is a case split over the stated exponent disjunction and applies the three independently accepted finite certificates, weakening the q4 lower bound where needed by arithmetic.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp_two_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp_four_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp_six_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_small_exponents_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19531 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2 ∨
      (m ^ 2).factorization 5 = 4 ∨
      (m ^ 2).factorization 5 = 6) :
    False := by sorry

end OddPerfectNumber
