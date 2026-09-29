-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_43_case_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_43_case_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T09:12:48.892213+00:00
-- url     : https://prove2.me/theorems/b6dddd5f-2eca-4d23-804c-6c527ca7a17b
-- title:
--   OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_43_case_v2
-- statement:
--   Weakened interface; identical proof.
-- source:
--   Weakened interface.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_43_D_le_84_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_large_D_q4_43_case_v2 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ (i)) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ (i)) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ (i)) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ (i)))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4eq : q4 = 43)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    D = 75 ∧ p = 149 := by
  sorry

end OddPerfectNumber
