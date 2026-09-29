-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_D_lt_45_canonical_absurd_v4
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_D_lt_45_canonical_absurd_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T02:32:16.942048+00:00
-- url     : https://prove2.me/theorems/e5633c5c-a731-4569-a48f-0a2764b10c58
-- title:
--   q3=13 low range is impossible at half floors
-- statement:
--   Under the canonical factor and sigma identities, D<45 with Euler-prime and fourth-prime conditions and half-exponent floors a>=1,b>=4,c>=1,e>=1, q3=13 is impossible by exact candidate enumeration and cross-multiplied minimum abundance.
-- source:
--   Weakened half-floor replacement of D_lt_45_canonical_absurd_v3; floors only feed ratio-lemma thresholds.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_D_lt_45_candidates_v2
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_two_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_base_le47

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_D_lt_45_canonical_absurd_v4 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D < 45) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hp_eq : p = 2 * D - 1) (hq4 : q4.Prime)
    (hq4gt : 13 < q4) (hq4dvd : q4 ∣ D)
    (ha : 1 ≤ a) (hb : 4 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
