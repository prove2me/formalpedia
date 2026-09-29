-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
-- name    : OddPerfectNumber.geom_ratio_lower_nineteen_ge_four
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T10:50:01.025086+00:00
-- url     : https://prove2.me/theorems/6cf83152-2b94-4260-b03c-525c9022c00a
-- title:
--   Cross-multiplied geometric lower bound for the 19-component at exponent four
-- statement:
--   For every exponent c>=4, the local geometric sum for 19^c is at least 137561/130321 times 19^c, in division-free cross-multiplied form.
-- source:
--   Exact cross-multiplication of the geometric-sum identity (19-1)S=19^(c+1)-1. The remaining inequality is 130321<=19^c, supplied by c>=4.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

namespace OddPerfectNumber

theorem geom_ratio_lower_nineteen_ge_four (c : Nat) (hc : 4 ≤ c) :
    137561 * 19 ^ c ≤
      130321 * (∑ i ∈ Finset.range (c + 1), 19 ^ i) := by
  sorry

end OddPerfectNumber
