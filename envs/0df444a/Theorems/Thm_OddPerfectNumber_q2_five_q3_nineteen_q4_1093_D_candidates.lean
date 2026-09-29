-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_1093_D_candidates
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_1093_D_candidates
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:46:42.839696+00:00
-- url     : https://prove2.me/theorems/a7f086ec-e892-40c1-897c-654db2fda9f5
-- title:
--   Finite half-successor candidates below 51 in the q4=1093 role
-- statement:
--   Odd half-successors below 51 with prime Euler companion and only the q4=1093 support primes as divisors have exactly six possibilities.
-- source:
--   Finite arithmetic candidate reduction for the q4=1093 exponent-six role.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_1093_D_candidates (D p : Nat)
    (hDlt : D < 51) (hDodd : Odd D) (hp : p.Prime)
    (hpeq : p = 2 * D - 1)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = 1093) :
    D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45 := by
  sorry

end OddPerfectNumber
