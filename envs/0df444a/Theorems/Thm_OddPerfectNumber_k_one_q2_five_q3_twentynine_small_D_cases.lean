-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-15T08:03:11.477095+00:00
-- url     : https://prove2.me/theorems/e07519df-34eb-4af3-af85-8df5350d2ce3
-- title:
--   Canonical q3=29 small-D candidates
-- statement:
--   For the canonical q2=5,q3=29 support envelope below D=75, odd D and prime p=2D-1 leave exactly D=27,31,37,45.
-- source:
--   Exclude every prime divisor outside {3,5,29} because q4>D, then perform bounded exact arithmetic on the remaining odd D values and p=2D-1.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_small_D_cases (D p q4 : Nat) (hDlt : D < 75) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) : D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 := by
  sorry

end OddPerfectNumber
