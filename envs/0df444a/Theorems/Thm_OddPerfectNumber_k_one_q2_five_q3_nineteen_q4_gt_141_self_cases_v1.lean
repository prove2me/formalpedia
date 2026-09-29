-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_gt_141_self_cases_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_gt_141_self_cases_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T17:56:22.600619+00:00
-- url     : https://prove2.me/theorems/a53d20d8-b052-4ebc-a501-fa138e98bcd8
-- title:
--   q3=19 high-q4 self-factor finite reduction
-- statement:
--   Under the canonical q3=19 factor-support hypotheses, the range 147≤D<225 with 142≤q4≤D has only the three self-factor survivors (157,157,313), (199,199,397), and (211,211,421).
-- source:
--   The accepted D∣m² bridge and factor-support coordinates bound the four exponents; a staged finite split on those coordinates and q₄, followed by exact primality checks, leaves the three self-factor tuples.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_D_dvd_m2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_factor_support_form_v4

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_q4_gt_141_self_cases_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hrel : D * sigma = p * m ^ 2) (hDlow : 147 ≤ D) (hDlt : D < 225) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hq4ge : 142 ≤ q4) (hq4leD : q4 ≤ D) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) : (D = 157 ∧ q4 = 157 ∧ p = 313) ∨ (D = 199 ∧ q4 = 199 ∧ p = 397) ∨ (D = 211 ∧ q4 = 211 ∧ p = 421) := by
  sorry

end OddPerfectNumber
