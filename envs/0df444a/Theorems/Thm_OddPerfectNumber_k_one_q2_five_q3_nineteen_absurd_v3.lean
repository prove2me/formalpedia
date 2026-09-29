-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_absurd_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T04:59:11.392012+00:00
-- url     : https://prove2.me/theorems/dd8d6688-1143-4b78-a267-b12dd64ec007
-- title:
--   Reduced q2=5 q3=19 four-support composition v3
-- statement:
--   Under the explicit accepted q3=19 reduced-case disjunction with the half-successor equation on both arms, either the canonical small-D envelope or the D=855,q4=101 terminal arm contradicts.
-- source:
--   Pure dispatch through the accepted canonical small-D and reduced large-D contradictions; the case disjunction is explicit and no canonical large-D reduction is asserted.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_absurd_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_absurd_v3 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hcase : ((D < 225 ∧ Odd D ∧ p.Prime ∧ p = 2 * D - 1 ∧ q4.Prime ∧ 19 < q4 ∧ D < q4 ∧ (∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) ∧ 4 ≤ a ∧ 3 ≤ b ∧ 2 ≤ c ∧ 1 ≤ e ∧ ((D = 57 ∧ 580 ≤ q4 ∧ q4 ≤ 602) ∨ (D = 75 ∧ 261 ≤ q4 ∧ q4 ≤ 264) ∨ (D = 135 ∧ 146 ≤ q4 ∧ q4 ≤ 148))) ∨ (D = 855 ∧ p = 2 * D - 1 ∧ q4 = 101 ∧ 1 ≤ e))) : False := by sorry

end OddPerfectNumber
