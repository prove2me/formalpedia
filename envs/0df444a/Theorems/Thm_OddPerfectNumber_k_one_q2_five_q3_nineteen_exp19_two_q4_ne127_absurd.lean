-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_q4_ne127_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_q4_ne127_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T05:12:20.305068+00:00
-- url     : https://prove2.me/theorems/ff767b4e-62ec-4afc-9382-031053c8c909
-- title:
--   The exponent-two 19-component is impossible when q4 is not 127
-- statement:
--   The accepted sigma(19^2) role split gives p=127 or q4=127. The first contradicts the odd-square half-successor equation and the second contradicts q4≠127.
-- source:
--   Compose the accepted 19^2 role theorem with the accepted p=127 odd-square contradiction and the explicit q4 inequality.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p127_hprod_odd_square_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp19_two_q4_ne127_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2)
    (hq4ne : q4 ≠ 127) :
    False := by
  sorry

end OddPerfectNumber
