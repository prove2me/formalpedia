-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_q4_cases_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_q4_cases_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T23:03:05.670948+00:00
-- url     : https://prove2.me/theorems/09450751-3a36-447c-8864-f2d020755a03
-- title:
--   q3=29 D=45 finite fourth-prime dispatcher
-- statement:
--   The two exact D=45 fourth-prime subcases q4=31 and q4=41 are both contradictory.
-- source:
--   Dispatch q4=31 to the accepted exact abundance terminal and q4=41 to the corrected modulo-89 source terminal.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_q4_31_abundance_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_q4_41_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D45_q4_cases_absurd (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 45) (hp_eq : p = 2 * D - 1)
    (hq4cases : q4 = 31 ∨ q4 = 41)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
