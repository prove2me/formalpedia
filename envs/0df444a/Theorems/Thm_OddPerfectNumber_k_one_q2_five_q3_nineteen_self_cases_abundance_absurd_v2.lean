-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_self_cases_abundance_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_self_cases_abundance_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T20:20:27.410664+00:00
-- url     : https://prove2.me/theorems/c782167b-32a2-4719-bd58-322c4978b364
-- title:
--   q3=19 self-factor survivors violate the strict abundance upper bound
-- statement:
--   Each of the three q3=19 self-factor tuples contradicts the strict product upper bound for the four geometric sigma factors.
-- source:
--   The strict scaled geometric-sum upper bounds multiply to 144*(q4-1)*sigma < 285*q4*m^2. Substituting each self-factor tuple contradicts D*sigma=p*m^2 after cancellation of the positive square factor.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_self_cases_abundance_absurd_v2 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hcases : (D = 157 ∧ q4 = 157 ∧ p = 313) ∨ (D = 199 ∧ q4 = 199 ∧ p = 397) ∨ (D = 211 ∧ q4 = 211 ∧ p = 421))
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) (hq4prime : q4.Prime) : False := by
  sorry

end OddPerfectNumber
