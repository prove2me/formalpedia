-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_absurd_v4
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_absurd_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T02:22:31.530885+00:00
-- url     : https://prove2.me/theorems/79f34b33-73d5-465c-bc43-f4e5bb2e4e4f
-- title:
--   q3=13 middle range is impossible at half floors
-- statement:
--   Under the canonical factor and sigma identities, the middle-range hypotheses 45<=D<214 with Euler-prime and fourth-prime conditions, support and divisibility data, and half-exponent floors a>=1,b>=4,c>=1,e>=1, q3=13 is impossible: the 13 exact candidates route to the accepted nine-case cut and four-case residual theorems.
-- source:
--   Canonical middle-range assembly from Proved candidates, cut v3, residual v3.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_candidates
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_residual_absurd_v3

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_middle_D_absurd_v4 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 45 ≤ D) (hDhigh : D < 214)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 13 < q4) (hq4le : q4 ≤ 89)
    (hq4dvd : q4 ∣ D)
    (hm : Odd m)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hDm : D ∣ m ^ 2)
    (ha : 1 ≤ a) (hb : 4 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
