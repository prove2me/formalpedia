-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le
-- name    : OddPerfectNumber.geom_sum_last_three_terms_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T18:11:52.277314+00:00
-- url     : https://prove2.me/theorems/ae4641b7-d49f-456f-9c69-ed223abe78b8
-- title:
--   The last three powers are bounded by their geometric sum
-- statement:
--   For exponent at least two, the final three powers occur in the finite geometric sum.
-- source:
--   Apply the accepted last-two-terms bound at exponent e-1 and append the final term of the sum.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

namespace OddPerfectNumber

theorem geom_sum_last_three_terms_le (q e : Nat) (he : 2 ≤ e) : q ^ e + q ^ (e - 1) + q ^ (e - 2) ≤ ∑ i ∈ Finset.range (e + 1), q ^ i := by sorry

end OddPerfectNumber
