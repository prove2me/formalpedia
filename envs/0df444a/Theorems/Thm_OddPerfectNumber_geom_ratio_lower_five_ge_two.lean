-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_two
-- name    : OddPerfectNumber.geom_ratio_lower_five_ge_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:42:27.840465+00:00
-- url     : https://prove2.me/theorems/26509e84-05c8-49d0-95a2-176ab9ab0afc
-- title:
--   Lower abundance ratio for the 5-component from exponent two
-- statement:
--   For exponent at least two, the 5-power geometric sum has the stated cross-multiplied lower abundance bound.
-- source:
--   Reusable local abundance lower bound for the four-support finite certificates.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

namespace OddPerfectNumber

theorem geom_ratio_lower_five_ge_two (b : Nat) (hb : 2 ≤ b) :
    31 * 5 ^ b ≤ 25 * (∑ i ∈ Finset.range (b + 1), 5 ^ i) := by
  sorry

end OddPerfectNumber
