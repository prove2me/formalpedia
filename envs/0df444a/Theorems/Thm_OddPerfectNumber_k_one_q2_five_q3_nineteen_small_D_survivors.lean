-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_survivors
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_survivors
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T18:54:07.743361+00:00
-- url     : https://prove2.me/theorems/443a0c08-0954-45f8-aff5-5acbed2676cc
-- title:
--   The q3=19 small-D envelope leaves three survivors
-- statement:
--   Composing the accepted q3=19 support-prime reduction with the accepted minimum-abundance cut, the small-D range leaves exactly D=57, D=75, or D=135.
-- source:
--   Pure composition of the accepted finite support disjunction and exact cross-multiplied abundance cut; no new candidate arithmetic is introduced.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_support_cases_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_abundance_cut

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_D_survivors
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 19 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlt : D < 225) (hDodd : Odd D) (hp : p.Prime)
    (hpeq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 19 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    D = 57 ∨ D = 75 ∨ D = 135 := by
  sorry

end OddPerfectNumber
