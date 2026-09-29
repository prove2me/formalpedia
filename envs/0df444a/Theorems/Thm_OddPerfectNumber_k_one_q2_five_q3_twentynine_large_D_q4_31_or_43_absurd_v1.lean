-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_31_or_43_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_31_or_43_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T08:06:38.727966+00:00
-- url     : https://prove2.me/theorems/9f7e12a7-7ea8-4b0d-826a-d232705ec01f
-- title:
--   Canonical q3=29 large-D q4=31 or 43 contradiction
-- statement:
--   The q3=29 large-D branch is impossible in the q4=31 or q4=43 canonical subcases by the accepted terminal contradictions.
-- source:
--   Pure dispatch over the accepted q4=31 and q4=43 canonical terminals.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_31_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_43_canonical_absurd_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_large_D_q4_31_or_43_absurd_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 29 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) (hcases : q4 = 31 ∨ q4 = 43) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : False := by
  sorry

end OddPerfectNumber
