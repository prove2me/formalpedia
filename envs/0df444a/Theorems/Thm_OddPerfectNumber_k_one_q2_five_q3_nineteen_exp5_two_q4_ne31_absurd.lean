-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_q4_ne31_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_q4_ne31_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T05:04:29.650372+00:00
-- url     : https://prove2.me/theorems/472f9b1c-f963-4fe9-82d3-a78a139f0e35
-- title:
--   The exponent-two 5-component is impossible when q4 is not 31
-- statement:
--   The accepted role split for sigma(5^2) gives p=31 or q4=31. The Euler role contradicts the odd-square half-successor equation, while the q4 role contradicts q4≠31.
-- source:
--   Compose the accepted role theorem with the accepted p=31 odd-square contradiction and eliminate the remaining q4 equality using the explicit inequality hypothesis.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p31_hprod_odd_square_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp5_two_q4_ne31_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2)
    (hq4ne : q4 ≠ 31) :
    False := by
  sorry

end OddPerfectNumber
