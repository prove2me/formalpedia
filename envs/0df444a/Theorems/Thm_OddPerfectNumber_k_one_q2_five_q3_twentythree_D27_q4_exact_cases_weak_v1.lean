-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_exact_cases_weak_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_exact_cases_weak_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T10:27:11.43464+00:00
-- url     : https://prove2.me/theorems/83f85f4b-7905-4109-8257-d02de70b4533
-- title:
--   OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_exact_cases_weak_v1
-- statement:
--   q23 D=27 exact fourth-prime triple under weak half-exponent floors, composing proved lower/upper/window.
-- source:
--   q23 small-D bridge; weak-floor composition.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_le_717
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_window_cases

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D27_q4_exact_cases_weak_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 27) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    q4 = 691 ∨ q4 = 701 ∨ q4 = 709 := by
  sorry

end OddPerfectNumber
