-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
-- name    : OddPerfectNumber.geom_ratio_lower_three_ge_eight
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T10:50:11.866731+00:00
-- url     : https://prove2.me/theorems/bb0d7da2-c841-4251-b098-f391301053a4
-- title:
--   Cross-multiplied geometric lower bound for the 3-component at exponent eight
-- statement:
--   For every exponent a>=8, the local geometric sum for 3^a is at least 9841/6561 times 3^a, in division-free cross-multiplied form.
-- source:
--   Exact cross-multiplication of the geometric-sum identity (3-1)S=3^(a+1)-1. The remaining inequality is 6561<=3^a, supplied by a>=8.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

namespace OddPerfectNumber

theorem geom_ratio_lower_three_ge_eight (a : Nat) (ha : 8 ≤ a) :
    9841 * 3 ^ a ≤
      6561 * (∑ i ∈ Finset.range (a + 1), 3 ^ i) := by
  sorry

end OddPerfectNumber
