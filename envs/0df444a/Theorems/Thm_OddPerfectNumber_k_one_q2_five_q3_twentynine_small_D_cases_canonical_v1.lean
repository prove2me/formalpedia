-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases_canonical_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_canonical_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T08:29:42.855675+00:00
-- url     : https://prove2.me/theorems/b00d7f93-77c6-4e32-9976-9306437a0750
-- title:
--   Canonical q3=29 small-D support cases
-- statement:
--   For the canonical q3=29 branch, odd D between 15 and 75, prime p=2D−1, and the exact D-support restriction leave only D=27,31,37,45; no ordering premise D<q4 is used.
-- source:
--   Finite canonical arithmetic with four short interval splits and explicit external-prime support contradictions.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_small_D_cases_canonical_v1 (D p q4 : Nat) (hDgt : 15 < D) (hDlt : D < 75) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) : D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 := by
  sorry

end OddPerfectNumber
