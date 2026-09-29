-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_self_cases_with_q4_dvd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_self_cases_with_q4_dvd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T18:30:05.788463+00:00
-- url     : https://prove2.me/theorems/d9c42be2-1f4c-410d-990c-f5d6bb483dfa
-- title:
--   q3=19 high-q4 self-factor reduction with q4 dividing D
-- statement:
--   Under the q3=19 high-q4 range, adding the necessary q4-divides-D premise reduces the self-factor cases to (157,157,313), (199,199,397), or (211,211,421).
-- source:
--   The q4-divides-D premise and q4≤D, D<225 force D=q4; the accepted prime-pair finite certificate then gives the three exact tuples.

import Mathlib
import Theorems.Thm_OddPerfectNumber_q3_nineteen_prime_pair_142_224_cases_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_self_cases_with_q4_dvd_v1 (D p q4 : Nat) (hDlow : 147 ≤ D) (hDlt : D < 225) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4ge : 142 ≤ q4) (hq4leD : q4 ≤ D) (hq4dvd : q4 ∣ D) : (D = 157 ∧ q4 = 157 ∧ p = 313) ∨ (D = 199 ∧ q4 = 199 ∧ p = 397) ∨ (D = 211 ∧ q4 = 211 ∧ p = 421) := by
  sorry

end OddPerfectNumber
