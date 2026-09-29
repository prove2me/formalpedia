-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_base_le47
-- name    : OddPerfectNumber.geom_ratio_lower_base_le47
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T01:16:22.106358+00:00
-- url     : https://prove2.me/theorems/4699ba71-2bab-4a61-a1bc-57d6be9f878c
-- title:
--   A geometric abundance bound for bases at most 47
-- statement:
--   When q≤47 and e≥2, the final two terms of the geometric sum give the exact lower ratio 48/47.
-- source:
--   Multiply the accepted final-two-terms bound by 47 and use q≤47 to compare q^e with 47 q^(e−1).

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

namespace OddPerfectNumber

theorem geom_ratio_lower_base_le47 (q e : Nat) (hq : q ≤ 47) (he : 2 ≤ e) :
    48 * q ^ e ≤ 47 * (∑ i ∈ Finset.range (e + 1), q ^ i) := by
  sorry

end OddPerfectNumber
