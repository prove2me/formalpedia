-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_le_43_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_le_43_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T04:53:15.729364+00:00
-- url     : https://prove2.me/theorems/7d23f58e-9956-475c-8f44-406aee59fa4b
-- title:
--   Canonical q3=29 large-D fourth-prime upper cut v2
-- statement:
--   Under the q2=5,q3=29 canonical factorization, strict local geometric upper bounds and D at least 75 force q4 at most 43.
-- source:
--   After the strict geometric upper bound, avoid nonlinear automation: primality rules out q4=44,45,46, and monotone integer cross-multiplication of q4≥47 and D≥75 contradicts the exact coefficient inequality.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_large_D_q4_le_43_v2 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 29 < q4) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : q4 ≤ 43 := by
  sorry

end OddPerfectNumber
