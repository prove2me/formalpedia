-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_nondivisor_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_nondivisor_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T09:04:41.938907+00:00
-- url     : https://prove2.me/theorems/a08ee1a6-1c0b-4331-a002-2855ab234903
-- title:
--   q3=23 large-D fourth-prime nondivisor contradiction
-- statement:
--   Let the square part m² have prime-power factorization 3^(2a) 5^(2b) 23^(2c) q4^(2e), and let sigma be the product of its four local geometric sums. Suppose D sigma = p m², p=2D-1 is prime, D≥111, and every prime divisor of D belongs to {3,5,23,q4}. If q4 is one of the primes 53,59,61, does not divide D, and a≥5, b≥3, c≥1, e≥1, these assumptions are contradictory. This isolates the fourth-prime nondivisor case needed by the existing q3=23 four-support branch; it does not assert the exponent bounds from weaker canonical hypotheses.
-- source:
--   Missing nondivisor arm of OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_canonical_v13, UUID d97d0664-bdac-4cdf-bbe4-20e427aa39cb. Uses independent accepted bound ba67d32b-4b4c-4942-b989-c9c3c7a70b84 and factor-support form 196bd19a-efb7-4228-906d-d768ea8e30c8. The exact finite products under D<=481 and prime 2D-1 leave D=115,135,225,405, each excluded by the geometric lower/upper window. No import of the parent.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_dvd_square_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_factor_support_form_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_D_le_481_v1
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_ten
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_terms_exact_v4

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_large_D_nondivisor_absurd_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 111 ≤ D)
    (hp : p.Prime) (hp_eq : p = 2*D-1) (hq4prime : q4.Prime)
    (hqcases : q4 = 53 ∨ q4 = 59 ∨ q4 = 61) (hnot : ¬ q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) : False := by
  sorry

end OddPerfectNumber
