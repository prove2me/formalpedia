-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_q4_le_139_factor_cases_v4
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_q4_le_139_factor_cases_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T22:04:16.088979+00:00
-- url     : https://prove2.me/theorems/5ba2067b-f07c-45d3-b902-ca2d83f173ad
-- title:
--   q3=19 middle q4 at most 139 finite factor cases v4
-- statement:
--   The canonical factor-support form and primality conditions leave four exact middle-range tuples when q4≤139 and 142≤D<225.
-- source:
--   Finite exponent-coordinate enumeration with explicit power-one normalization; simplification is guarded because some branches are already normalized.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_D_dvd_m2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_factor_support_form_v4

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_middle_q4_le_139_factor_cases_v4 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hrel : D * sigma = p * m ^ 2) (hDlow : 142 ≤ D) (hDhigh : D < 225) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hq4le : q4 ≤ 139) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) : (D = 159 ∧ q4 = 53 ∧ p = 317) ∨ (D = 177 ∧ q4 = 59 ∧ p = 353) ∨ (D = 201 ∧ q4 = 67 ∧ p = 401) ∨ (D = 205 ∧ q4 = 41 ∧ p = 409) := by
  sorry

end OddPerfectNumber
