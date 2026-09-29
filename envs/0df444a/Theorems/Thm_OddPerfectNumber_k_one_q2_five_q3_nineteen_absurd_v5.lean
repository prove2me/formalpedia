-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_absurd_v5
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_v5
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T00:50:07.970815+00:00
-- url     : https://prove2.me/theorems/7888161a-c527-4197-ada2-920e4d8e63b8
-- title:
--   Canonical q3=19 four-support contradiction
-- statement:
--   The canonical q2=5, q3=19 branch is contradicted by the accepted small-D and large-D canonical terminals.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_canonical_absurd_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_absurd_v5 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  sorry

end OddPerfectNumber
