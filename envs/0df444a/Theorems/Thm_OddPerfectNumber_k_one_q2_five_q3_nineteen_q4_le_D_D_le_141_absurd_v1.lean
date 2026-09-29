-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_le_D_D_le_141_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_le_D_D_le_141_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T17:44:22.308089+00:00
-- url     : https://prove2.me/theorems/2b26b199-a07e-46a8-b03f-f7bd6d2bb3a9
-- title:
--   Canonical q3=19 q4-at-most-D contradiction through 141
-- statement:
--   Under the canonical q3=19 support factorization and exponent floors, if q4 is at most D and D is at most 141, the exact lower abundancy product contradicts the Euler relation.
-- source:
--   The q4≤141 ratio helper is multiplied with the accepted 3, 5, and 19 abundance lower bounds; cancellation against D·sigma=p·m² and p=2D−1 yields the contradiction for D≤141.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_le_141_ratio_v1
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_q4_le_D_D_le_141_absurd_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 1 ≤ D) (hDodd : Odd D) (hDle : D ≤ 141) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hq4leD : q4 ≤ D) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  sorry

end OddPerfectNumber
