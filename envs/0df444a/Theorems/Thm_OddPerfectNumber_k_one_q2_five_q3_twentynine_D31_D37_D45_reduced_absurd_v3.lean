-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D31_D37_D45_reduced_absurd_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D31_D37_D45_reduced_absurd_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T03:06:17.495908+00:00
-- url     : https://prove2.me/theorems/548bc73c-4666-4b18-80a3-12a5e0530645
-- title:
--   q3=29 parity-free D31 D37 D45 dispatcher
-- statement:
--   The exact D=31, D=37, and D=45 q3=29 terminal dispatcher, with no unnecessary parity premises.
-- source:
--   Explicitly destructure the three D cases and consume the parity-free D31/D37 terminals and accepted D45 q4 dispatcher.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D31_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D37_absurd_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_q4_cases_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D31_D37_D45_reduced_absurd_v3 (m d D p q4 sigma a b c e : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDcases : D = 31 ∨ D = 37 ∨ D = 45) (hp_eq : p = 2 * D - 1) (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) (hddvd : d ∣ m ^ 2) (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) (hq4prime : q4.Prime) (hD45q4 : D = 45 → q4 = 31 ∨ q4 = 41) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : False := by
  sorry

end OddPerfectNumber
