-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_reduced_source_dispatch
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_reduced_source_dispatch
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T21:11:13.846558+00:00
-- url     : https://prove2.me/theorems/222e44d2-375a-4013-9126-7d39e18f5f34
-- title:
--   The accepted q3=19 finite source arms dispatch
-- statement:
--   The accepted D=57 source dispatch, q4=101 p=1709 source obstruction, and D=135 prime exclusion eliminate their supplied finite alternatives.
-- source:
--   Finite dispatch only; the D=75 arm and canonical candidate generation remain explicit upstream obligations.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_source_dispatch
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_101_source_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D135_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_reduced_source_dispatch (sigma a b c e q4 : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hcase :
      ((q4 = 587 ∧ 113 ∣ sigma) ∨ (q4 = 593 ∧ 593 ∣ sigma) ∨
        (q4 = 599 ∧ 113 ∣ sigma) ∨ (q4 = 601 ∧ 113 ∣ sigma)) ∨
      (q4 = 101 ∧ 1709 ∣ sigma ∧
        Even (orderOf (3 : ZMod 1709)) ∧ Even (orderOf (5 : ZMod 1709)) ∧
        Even (orderOf (19 : ZMod 1709)) ∧ Even (orderOf (101 : ZMod 1709))) ∨
      (q4.Prime ∧ 146 ≤ q4 ∧ q4 ≤ 148)) :
    False := by
  sorry

end OddPerfectNumber
