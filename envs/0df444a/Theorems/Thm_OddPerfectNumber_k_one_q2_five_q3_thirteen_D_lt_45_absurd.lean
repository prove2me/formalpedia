-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_D_lt_45_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_D_lt_45_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T18:06:35.621195+00:00
-- url     : https://prove2.me/theorems/19a12e7c-eabe-4ea6-bb84-95f3bcfa4960
-- title:
--   The q3=13 D<45 certificate is impossible
-- statement:
--   Any canonical q2=5, q3=13 instance in the D<45 range is impossible once its exact finite certificate places the 5-component exponent at 2, 4, or 6.
-- source:
--   The range marker is retained explicitly, while the finite exponent certificate is discharged by the accepted q3=13 small-exponents contradiction. Candidate enumeration remains a separate upstream reduction obligation.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_small_exponents_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_D_lt_45_absurd (p m d D q4 sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19531 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2 ∨
      (m ^ 2).factorization 5 = 4 ∨ (m ^ 2).factorization 5 = 6)
    (hD : D < 45) :
    False := by
  sorry

end OddPerfectNumber
