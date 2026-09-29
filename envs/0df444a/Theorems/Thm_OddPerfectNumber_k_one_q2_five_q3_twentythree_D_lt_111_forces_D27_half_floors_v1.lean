-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_forces_D27_half_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_forces_D27_half_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T10:23:29.059498+00:00
-- url     : https://prove2.me/theorems/97334bc0-cfee-4c16-87cd-e7ec4e6681d2
-- title:
--   OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_forces_D27_half_floors_v1
-- statement:
--   q23 weak-floor forces_D27: support_cases plus D37915, D45D69, D75 eliminations.
-- source:
--   q23 small-D bridge; weak-floor composition.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D37915_weak_floor_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D75_absurd_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D_lt_111_forces_D27_half_floors_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    D = 27 := by
  sorry

end OddPerfectNumber
