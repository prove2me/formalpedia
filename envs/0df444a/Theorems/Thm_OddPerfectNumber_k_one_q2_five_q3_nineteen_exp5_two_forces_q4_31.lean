-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_forces_q4_31
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_forces_q4_31
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T22:45:07.050459+00:00
-- url     : https://prove2.me/theorems/6154ee31-2c56-46e5-bfcd-6f188c4c269d
-- title:
--   The exponent-two 5-component forces fourth support prime 31
-- statement:
--   The accepted 5² role theorem gives p=31 or q4=31. The p=31 case makes 16 divide the odd square m² and is impossible, so q4=31.
-- source:
--   Apply the accepted role theorem. If p=31, invoke the accepted odd-square parity contradiction; otherwise the role disjunction directly yields q4=31.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p31_hprod_odd_square_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp5_two_forces_q4_31 (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2) :
    q4 = 31 := by sorry

end OddPerfectNumber
