-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T04:50:19.946982+00:00
-- url     : https://prove2.me/theorems/4afaa3ed-158e-4f5b-a673-aa8e2bc643f5
-- title:
--   Reduced q2=5 q3=19 four-support composition
-- statement:
--   Under the explicit accepted q3=19 reduced-case disjunction, either the canonical small-D envelope or the D=855,q4=101 terminal arm contradicts.
-- source:
--   Pure dispatch through the accepted canonical small-D and reduced large-D contradictions; no canonical D-range reduction is asserted.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_absurd_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_absurd_v2 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hcase : ((D < 225 ∧ Odd D ∧ p.Prime ∧ p = 2 * D - 1 ∧ q4.Prime ∧ 19 < q4 ∧ D < q4 ∧ (∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) ∧ 4 ≤ a ∧ 3 ≤ b ∧ 2 ≤ c ∧ 1 ≤ e ∧ ((D = 57 ∧ 580 ≤ q4 ∧ q4 ≤ 602) ∨ (D = 75 ∧ 261 ≤ q4 ∧ q4 ≤ 264) ∨ (D = 135 ∧ 146 ≤ q4 ∧ q4 ≤ 148))) ∨ (D = 855 ∧ q4 = 101 ∧ 1 ≤ e))) : False := by sorry

end OddPerfectNumber
