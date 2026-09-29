-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D_lt_75_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D_lt_75_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T03:37:33.771242+00:00
-- url     : https://prove2.me/theorems/21fd5f85-0d74-41a0-b405-4cfd96f75497
-- title:
--   Canonical q3=29 small-D contradiction
-- statement:
--   Under the canonical q2=5, q3=29 hypotheses and 15<D<75, the finite D=31,37,45 dispatch contradicts the branch.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D_lt_75_absurd_v1 (m d D p q4 sigma a b c e : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDgt : 15 < D) (hDlt : D < 75) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hp4 : p % 4 = 1) (hq4prime : q4.Prime) (hq4gt : 29 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) (hddvd : d ∣ m ^ 2) (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) (hD45q4 : D = 45 → q4 = 31 ∨ q4 = 41) : False := by sorry

end OddPerfectNumber
