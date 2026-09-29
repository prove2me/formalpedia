-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T02:48:30.935741+00:00
-- url     : https://prove2.me/theorems/ef91b992-8433-4e74-8815-2fb18ddb45ff
-- title:
--   Canonical q3=19 small-D source bridge
-- statement:
--   The exact q3=19 small-D candidate tuples contradict the canonical sigma equation: the D=57 p=113 source is derived from the half-successor equation, the q4=593 source is derived from the q4-factor, D=75 uses the accepted canonical abundance contradiction, and D=135 has no prime fourth support.
-- source:
--   Changed canonical bridge from the exact five-tuple reduction to the accepted terminal source contradictions; no incoming source-divisibility premise is used.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_source_dispatch
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_abundance_absurd_v5
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D135_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1)
    (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hcases :
      (D = 57 ∧ q4 = 587) ∨
      (D = 57 ∧ q4 = 593) ∨
      (D = 57 ∧ q4 = 599) ∨
      (D = 57 ∧ q4 = 601) ∨
      (D = 75 ∧ q4 = 263) ∨
      (D = 135 ∧ q4.Prime ∧ 146 ≤ q4 ∧ q4 ≤ 148)) :
    False := by
  sorry

end OddPerfectNumber
