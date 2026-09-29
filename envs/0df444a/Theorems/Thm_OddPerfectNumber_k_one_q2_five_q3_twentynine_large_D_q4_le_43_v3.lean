-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_le_43_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_le_43_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T04:58:33.639802+00:00
-- url     : https://prove2.me/theorems/692a0194-3564-4afe-84ca-e798d909dbe8
-- title:
--   Canonical q3=29 large-D fourth-prime upper cut v3
-- statement:
--   Under the q2=5,q3=29 canonical factorization, strict local geometric upper bounds and D at least 75 force q4 at most 43.
-- source:
--   The v3 source retains the explicit monotone multiplication proof and replaces only the remaining constant-coefficient nlinarith step by omega.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_large_D_q4_le_43_v3 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 29 < q4) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : q4 ≤ 43 := by
  sorry

end OddPerfectNumber
