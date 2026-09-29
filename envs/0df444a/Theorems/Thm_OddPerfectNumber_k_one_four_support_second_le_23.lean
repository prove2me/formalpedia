-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_four_support_second_le_23
-- name    : OddPerfectNumber.k_one_four_support_second_le_23
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T13:44:48.278179+00:00
-- url     : https://prove2.me/theorems/93337d6f-2280-471e-818d-c5d375a1caeb
-- title:
--   Second support prime bound in the k=1 four-support case
-- statement:
--   In the canonical k=1 equations, four strictly ordered prime support elements with smallest prime 3 have second prime at most 23.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem OddPerfectNumber.k_one_four_support_second_le_23 (p m d q1 q2 q3 q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : m.primeFactors = {q1, q2, q3, q4})
    (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime) (hq4 : q4.Prime)
    (horder : q1 < q2 ∧ q2 < q3 ∧ q3 < q4)
    (hq1eq : q1 = 3) :
    q2 ≤ 23 := by sorry
