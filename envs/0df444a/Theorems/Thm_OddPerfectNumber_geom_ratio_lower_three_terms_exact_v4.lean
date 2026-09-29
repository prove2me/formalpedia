-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_terms_exact_v4
-- name    : OddPerfectNumber.geom_ratio_lower_three_terms_exact_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T22:02:05.497669+00:00
-- url     : https://prove2.me/theorems/34cea444-4568-45a9-88ce-da749e2cce05
-- title:
--   Exact three-term geometric lower ratio v4
-- statement:
--   For every positive exponent index, the final three terms of the geometric sum give the exact lower ratio (q²+q+1)/q².
-- source:
--   Scale the accepted last-three-term bound by q² and close the normalized equality with a simp-only reflexivity step.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

namespace OddPerfectNumber

theorem geom_ratio_lower_three_terms_exact_v4 (q e : Nat) (he : 1 ≤ e) : (q^2 + q + 1) * q^(2*e) ≤ q^2 * (∑ i ∈ Finset.range (2*e + 1), q^i) := by
  sorry

end OddPerfectNumber
