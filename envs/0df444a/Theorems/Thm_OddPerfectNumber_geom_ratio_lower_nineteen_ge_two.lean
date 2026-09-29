-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_two
-- name    : OddPerfectNumber.geom_ratio_lower_nineteen_ge_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T23:46:52.621469+00:00
-- url     : https://prove2.me/theorems/1ef3d65e-dd18-4fa7-870d-43c5f6cd51f0
-- title:
--   Cross-multiplied geometric lower bound for the 19-component
-- statement:
--   For every exponent c≥2, the local geometric sum for 19^c is at least 381/361 times 19^c, in integral cross-multiplied form.
-- source:
--   Exact telescoping and integer arithmetic for the 19-component abundance factor.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

namespace OddPerfectNumber

theorem geom_ratio_lower_nineteen_ge_two (c : Nat) (hc : 2 ≤ c) :
    381 * 19 ^ c ≤
      361 * (∑ i ∈ Finset.range (c + 1), 19 ^ i) := by
  sorry

end OddPerfectNumber
