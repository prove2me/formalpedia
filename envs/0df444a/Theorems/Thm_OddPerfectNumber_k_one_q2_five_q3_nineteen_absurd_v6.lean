-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_absurd_v6
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_v6
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T07:59:59.831356+00:00
-- url     : https://prove2.me/theorems/032cf8a5-9aaf-4cad-99a9-121a9566c876
-- title:
--   Canonical q3=19 branch contradiction
-- statement:
--   The canonical q2=5, q3=19 four-support branch is impossible.
-- source:
--   Split at D=147 and D=225. The accepted canonical D<147 terminal handles the first range, and the accepted canonical middle terminal handles 147≤D<225. In the remaining case 225≤D, consume the accepted canonical large-D terminal.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_lt_147_absurd_canonical_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_D_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_canonical_absurd_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_absurd_v6 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  sorry

end OddPerfectNumber
