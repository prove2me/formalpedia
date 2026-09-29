-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases_canonical_v4
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_canonical_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T08:57:09.111537+00:00
-- url     : https://prove2.me/theorems/08aabb71-f82d-448d-a209-4b5c1cc43e84
-- title:
--   Canonical q3=29 small-D support cases v4
-- statement:
--   The canonical q3=29 small-D support enumeration, with an exhaustive bounded D split and no D<q4 premise.
-- source:
--   Exhaustive finite D split after deriving the exact 16≤D≤74 bounds; composite Euler primes and unsupported prime divisors are discharged separately.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_small_D_cases_canonical_v4 (D p q4 : Nat) (hDgt : 15 < D) (hDlt : D < 75) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) : D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 := by
  sorry

end OddPerfectNumber
