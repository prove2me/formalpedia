-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_terms_exact_v1
-- name    : OddPerfectNumber.geom_ratio_lower_three_terms_exact_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T21:23:05.023752+00:00
-- url     : https://prove2.me/theorems/ff3b27b9-a9b2-4810-af09-348e59044f19
-- title:
--   Exact three-term geometric lower ratio
-- statement:
--   For every positive exponent index, the final three terms of the geometric sum give the exact lower ratio (q²+q+1)/q².
-- source:
--   Scale the accepted last-three-term bound by q² and normalize the two power identities.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

namespace OddPerfectNumber

theorem geom_ratio_lower_three_terms_exact_v1 (q e : Nat) (he : 1 ≤ e) : (q^2 + q + 1) * q^(2*e) ≤ q^2 * (∑ i ∈ Finset.range (2*e + 1), q^i) := by
  sorry

end OddPerfectNumber
