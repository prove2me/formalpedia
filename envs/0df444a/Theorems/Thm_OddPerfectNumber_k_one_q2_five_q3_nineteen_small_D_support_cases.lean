-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_support_cases
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_support_cases
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-14T09:45:19.580166+00:00
-- url     : https://prove2.me/theorems/80b86947-6e97-4329-a80c-2abd9400a179
-- title:
--   The q2=5 q3=19 small-D support enumeration
-- statement:
--   For D below 225 with odd D, prime half-successor p = 2D-1, fourth prime above 19, and all prime divisors of D in {3,5,19,q4}, D is one of 3,9,15,19,27,45,57,75,135.
-- source:
--   Finite support-plus-primality enumeration mirroring the accepted q4=1093 D-candidates pattern at bound 225; the abundance cut to {57,75} is a separate theorem.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_D_support_cases (D p q4 : Nat)
    (hDlt : D < 225) (hDodd : Odd D) (hp : p.Prime)
    (hpeq : p = 2 * D - 1) (hq4gt : 19 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) :
    D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45 ∨ D = 57 ∨ D = 75 ∨ D = 135 := by
  sorry

end OddPerfectNumber
