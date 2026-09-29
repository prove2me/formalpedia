-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
-- name    : OddPerfectNumber.geom_ratio_lower_five_ge_six
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T03:09:11.553207+00:00
-- url     : https://prove2.me/theorems/f5036442-93f6-4ec1-843d-70a05e99e2bf
-- title:
--   Five-component abundance lower bound from exponent six
-- statement:
--   For exponent at least six, the 5-power geometric sum has the stated five-term cross-multiplied abundance lower bound.
-- source:
--   Reusable stronger five-component abundance bound for the q3=19 q4=1093 finite certificate.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

namespace OddPerfectNumber

theorem geom_ratio_lower_five_ge_six (b : Nat) (hb : 6 ≤ b) :
    3906 * 5 ^ b ≤ 3125 * (∑ i ∈ Finset.range (b + 1), 5 ^ i) := by
  sorry

end OddPerfectNumber
