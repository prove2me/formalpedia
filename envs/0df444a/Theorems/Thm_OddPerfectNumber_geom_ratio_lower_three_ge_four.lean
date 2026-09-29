-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_four
-- name    : OddPerfectNumber.geom_ratio_lower_three_ge_four
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T00:26:16.496062+00:00
-- url     : https://prove2.me/theorems/fec9deb4-8fb9-4e67-8070-4f5b4bf48726
-- title:
--   Lower abundance ratio for the 3-component from exponent four
-- statement:
--   For every exponent a at least four, the 3-power geometric sum has ratio at least 121/81.
-- source:
--   Exact geometric identity and monotonicity of powers.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

namespace OddPerfectNumber

theorem geom_ratio_lower_three_ge_four (a : Nat) (ha : 4 ≤ a) :
    121 * 3 ^ a ≤
      81 * (∑ i ∈ Finset.range (a + 1), 3 ^ i) := by
  sorry

end OddPerfectNumber
