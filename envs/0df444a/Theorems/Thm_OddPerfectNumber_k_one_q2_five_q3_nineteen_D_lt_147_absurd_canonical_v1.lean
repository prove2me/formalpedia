-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_lt_147_absurd_canonical_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_D_lt_147_absurd_canonical_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T19:33:26.073108+00:00
-- url     : https://prove2.me/theorems/bc9598e5-2666-4625-a227-477d59108c1f
-- title:
--   Canonical q3=19 contradiction below D=147
-- statement:
--   Under the canonical q2=5 q3=19 hypotheses, the range D<147 is impossible without assuming q4 divides D.
-- source:
--   This is a source-faithful canonical composition. Split on q4≤D. The q4≤D arm has D≤141 after eliminating the five odd boundary values 142–146 by primality/parity. The D<q4 arm consumes the already published survivor, q4-window, and canonical small-D source terminals.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_le_D_D_le_141_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_survivors
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_q4_ranges_v6
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_D_lt_147_absurd_canonical_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlt : D < 147) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  sorry

end OddPerfectNumber
