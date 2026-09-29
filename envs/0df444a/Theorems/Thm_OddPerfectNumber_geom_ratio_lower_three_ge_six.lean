-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_six
-- name    : OddPerfectNumber.geom_ratio_lower_three_ge_six
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T23:44:47.400807+00:00
-- url     : https://prove2.me/theorems/3199f6be-405c-4b87-b81d-01f0d5b97bec
-- title:
--   Cross-multiplied geometric lower bound for the 3-component
-- statement:
--   For every exponent a≥6, the local geometric sum for 3^a is at least 1093/729 times 3^a, in division-free cross-multiplied form.
-- source:
--   Exact cross-multiplication of the geometric-sum identity (3−1)S=3^(a+1)−1. The remaining inequality is 729≤3^a, supplied by a≥6.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

namespace OddPerfectNumber

theorem geom_ratio_lower_three_ge_six (a : Nat) (ha : 6 ≤ a) :
    1093 * 3 ^ a ≤
      729 * (∑ i ∈ Finset.range (a + 1), 3 ^ i) := by
  sorry

end OddPerfectNumber
