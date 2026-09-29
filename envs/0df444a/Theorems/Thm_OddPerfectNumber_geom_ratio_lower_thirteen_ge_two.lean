-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two
-- name    : OddPerfectNumber.geom_ratio_lower_thirteen_ge_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:42:33.484384+00:00
-- url     : https://prove2.me/theorems/6f651d07-485b-48eb-970f-377dcbadb1be
-- title:
--   Lower abundance ratio for the 13-component from exponent two
-- statement:
--   For exponent at least two, the 13-power geometric sum has the stated cross-multiplied lower abundance bound.
-- source:
--   Reusable local abundance lower bound for the four-support finite certificates.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

namespace OddPerfectNumber

theorem geom_ratio_lower_thirteen_ge_two (c : Nat) (hc : 2 ≤ c) :
    183 * 13 ^ c ≤ 169 * (∑ i ∈ Finset.range (c + 1), 13 ^ i) := by
  sorry

end OddPerfectNumber
