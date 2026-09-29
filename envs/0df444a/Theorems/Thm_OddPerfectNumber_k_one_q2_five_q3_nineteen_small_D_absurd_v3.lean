-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_absurd_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_absurd_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T00:45:40.686729+00:00
-- url     : https://prove2.me/theorems/b61cbe13-1dcd-4391-8725-099a2406f295
-- title:
--   The q3=19 reduced small-D source cases are impossible (v3)
-- statement:
--   The exact reduced q3=19 small-D source alternatives at D=57, D=75, and D=135 each contradict an accepted terminal certificate; v3 uses the stronger D=75 theorem that derives its own 263 source.
-- source:
--   Changed finite dispatch replacement after the prior queue-state race; the D=75 branch no longer carries an incoming 263-divisibility binder.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_source_dispatch
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_abundance_absurd_v5
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D135_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_D_absurd_v3
    (sigma a b c e q4 D : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hcases : (D = 57 ∧ ((q4 = 587 ∧ 113 ∣ sigma) ∨ (q4 = 593 ∧ 593 ∣ sigma) ∨ (q4 = 599 ∧ 113 ∣ sigma) ∨ (q4 = 601 ∧ 113 ∣ sigma))) ∨
      (D = 75 ∧ q4 = 263 ∧ (∃ m a' b' c' e', m ^ 2 = 3 ^ (2 * a') * 5 ^ (2 * b') * 19 ^ (2 * c') * 263 ^ (2 * e') ∧ sigma = (∑ i ∈ Finset.range (2 * a' + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b' + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c' + 1), 19 ^ i) * (∑ i ∈ Finset.range (2 * e' + 1), 263 ^ i) ∧ 75 * sigma = 149 * m ^ 2 ∧ 3 ≤ b' ∧ 2 ≤ c' ∧ 1 ≤ e')) ∨
      (D = 135 ∧ q4.Prime ∧ 146 ≤ q4 ∧ q4 ≤ 148)) :
    False := by
  sorry

end OddPerfectNumber
