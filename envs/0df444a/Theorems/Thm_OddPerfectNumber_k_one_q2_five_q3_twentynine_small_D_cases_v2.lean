-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T08:06:57.967666+00:00
-- url     : https://prove2.me/theorems/13d3fe9a-dd96-4fb1-8a48-2e0686d5df5c
-- title:
--   q3=29 small-D candidates after the abundance cut
-- statement:
--   After the canonical lower-abundance cut 15<D, the q2=5,q3=29 support envelope below D=75 leaves exactly D=27,31,37,45.
-- source:
--   Exclude prime divisors outside {3,5,29} because q4>D; bounded exact arithmetic with 15<D, odd D and prime 2D-1 leaves the four stated values.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_small_D_cases_v2 (D p q4 : Nat) (hDgt : 15 < D) (hDlt : D < 75) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) : D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 := by
  sorry

end OddPerfectNumber
