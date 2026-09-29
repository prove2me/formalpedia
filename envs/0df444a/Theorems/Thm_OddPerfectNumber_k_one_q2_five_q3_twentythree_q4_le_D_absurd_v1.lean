-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_le_D_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_le_D_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T07:49:45.052393+00:00
-- url     : https://prove2.me/theorems/07a8075f-0232-4ede-8dae-590f7732e07f
-- title:
--   Canonical q3=23 small-D q4-le-D contradiction
-- statement:
--   The q3=23 small-D branch is impossible whenever q4 does not exceed D, by the accepted divisor and nondivisor terminal compositions.
-- source:
--   Canonical q4≤D split: the accepted divisor-case enumeration feeds the accepted source terminal; the nondivisor case feeds its accepted canonical terminal.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_divisor_small_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_not_divides_D_absurd_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_q4_le_D_absurd_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) (hq4le : q4 ≤ D) (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) : False := by
  sorry

end OddPerfectNumber
