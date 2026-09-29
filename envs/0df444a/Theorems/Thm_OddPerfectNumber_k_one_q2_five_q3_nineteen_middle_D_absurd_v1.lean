-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_D_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_D_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T07:52:12.404152+00:00
-- url     : https://prove2.me/theorems/5927e562-d1aa-4bea-a7fa-988b36abb7ba
-- title:
--   Canonical q3=19 middle range contradiction
-- statement:
--   The canonical q3=19 branch is impossible in the middle range 147≤D<225.
-- source:
--   Split the middle range at D=147, at q4≤D, and at q4=142. The accepted canonical D<147 terminal handles the first part. If q4>D, consume the strict q4>D abundance contradiction. If q4≤D and q4<142, primality excludes 140 and 141, so q4≤139 and the ratio contradiction applies. For q4≥142, the accepted finite self-case reduction gives three tuples, each eliminated by the accepted strict abundance terminal.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_lt_147_absurd_canonical_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_q4_le_139_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_q4_gt_D_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_gt_141_self_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_self_cases_abundance_absurd_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_middle_D_absurd_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlt225 : D < 225) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  sorry

end OddPerfectNumber
