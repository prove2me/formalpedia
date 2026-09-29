-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T00:32:05.717352+00:00
-- url     : https://prove2.me/theorems/c742884c-cdd4-41e2-a086-8b4e64e0855a
-- title:
--   The q3=19 reduced small-D source cases are impossible (v2)
-- statement:
--   The exact reduced q3=19 small-D source alternatives at D=57, D=75, and D=135 each contradict an accepted terminal certificate; canonical source generation remains an upstream obligation.
-- source:
--   Pure dispatch through accepted D=57 source, D=75 abundance, and D=135 prime-interval contradictions.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_source_dispatch
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_abundance_absurd_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D135_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_D_absurd_v2
    (sigma a b c e q4 D : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hcases : (D = 57 ∧ ((q4 = 587 ∧ 113 ∣ sigma) ∨ (q4 = 593 ∧ 593 ∣ sigma) ∨ (q4 = 599 ∧ 113 ∣ sigma) ∨ (q4 = 601 ∧ 113 ∣ sigma))) ∨
      (D = 75 ∧ q4 = 263 ∧ (∃ m a' b' c' e', m ^ 2 = 3 ^ (2 * a') * 5 ^ (2 * b') * 19 ^ (2 * c') * 263 ^ (2 * e') ∧ sigma = (∑ i ∈ Finset.range (2 * a' + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b' + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c' + 1), 19 ^ i) * (∑ i ∈ Finset.range (2 * e' + 1), 263 ^ i) ∧ 75 * sigma = 149 * m ^ 2 ∧ 263 ∣ sigma ∧ 3 ≤ b' ∧ 2 ≤ c' ∧ 1 ≤ e')) ∨
      (D = 135 ∧ q4.Prime ∧ 146 ≤ q4 ∧ q4 ≤ 148)) :
    False := by
  sorry

end OddPerfectNumber
