-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_seventeen_ge_two
-- name    : OddPerfectNumber.geom_ratio_lower_seventeen_ge_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T12:01:00.515933+00:00
-- url     : https://prove2.me/theorems/f8051f21-613f-4889-a79c-2fc0aa1fa9bb
-- title:
--   Cross-multiplied geometric lower bound for the 17-component
-- statement:
--   For c >= 2, 307*17^c <= 289*sum_{i<=c} 17^i.
-- source:
--   Seventeen-component abundance lower bound for q17 windows; mirrors proved nineteen analogue (381/361).

import Mathlib

namespace OddPerfectNumber

theorem geom_ratio_lower_seventeen_ge_two (c : Nat) (hc : 2 ≤ c) :
    307 * 17 ^ c ≤
      289 * (∑ i ∈ Finset.range (c + 1), 17 ^ i) := by
  sorry

end OddPerfectNumber
