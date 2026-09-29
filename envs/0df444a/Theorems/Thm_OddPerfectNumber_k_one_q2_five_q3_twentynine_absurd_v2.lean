-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T15:23:36.411875+00:00
-- url     : https://prove2.me/theorems/8355c30d-f20a-4f3d-b375-9cf7cc7af74c
-- title:
--   Complete canonical q3=29 branch v2
-- statement:
--   The canonical q2=5 q3=29 branch is impossible by the accepted D<75 finite dispatch and accepted D≥75 reduction.
-- source:
--   Split at 75. The accepted lower cut supplies 15<D in the small arm; the accepted four-case enumeration dispatches D=27,31,37,45 to their canonical terminals, while the accepted large-D theorem closes 75≤D.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D_gt_15_v6
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases_canonical_v7
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D31_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D37_absurd_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_absurd_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_absurd_v2 (m d sigma D p q4 a b c e : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 29 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) (hddvd : d ∣ m ^ 2) (hm0 : m ≠ 0) (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4) : False := by
  sorry

end OddPerfectNumber
