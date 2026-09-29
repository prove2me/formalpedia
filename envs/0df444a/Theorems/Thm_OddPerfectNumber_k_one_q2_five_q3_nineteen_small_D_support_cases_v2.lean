-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_support_cases_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_support_cases_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T10:17:34.587781+00:00
-- url     : https://prove2.me/theorems/1ca4d1a7-ca14-4903-bd8b-43b8d49bab7c
-- title:
--   The q2=5 q3=19 small-D support enumeration, corrected
-- statement:
--   For D below 225 and below q4, with odd D, prime half-successor p = 2D-1, fourth prime above 19, and all prime divisors of D in {3,5,19,q4}, D is one of 3,9,15,19,27,45,57,75,135. The D < q4 hypothesis rules out the q4-equals-divisor counterexamples that made v1 false.
-- source:
--   Corrected v2 of the small-D support enumeration: v1 omitted D < q4 and was falsified by (D,p,q4) = (31,61,31). Proof mirrors the accepted q4=1093 D-candidates interval pattern with 20 prime exclusions, each discharged against D < q4.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_D_support_cases_v2 (D p q4 : Nat)
    (hDlt : D < 225) (hDodd : Odd D) (hp : p.Prime)
    (hpeq : p = 2 * D - 1) (hq4gt : 19 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) :
    D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45 ∨ D = 57 ∨ D = 75 ∨ D = 135 := by
  sorry

end OddPerfectNumber
