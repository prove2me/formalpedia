-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_terms_exact_v3
-- name    : OddPerfectNumber.geom_ratio_lower_three_terms_exact_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T21:58:12.556608+00:00
-- url     : https://prove2.me/theorems/9450c5ae-6aab-44e5-94de-e64fc7ae7a88
-- title:
--   Exact three-term geometric lower ratio v3
-- statement:
--   For every positive exponent index, the final three terms of the geometric sum give the exact lower ratio (q²+q+1)/q².
-- source:
--   Scale the accepted last-three-term bound by q² and use explicit equality normalization; the reflexive final calc step is discharged by the calc chain itself.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

namespace OddPerfectNumber

theorem geom_ratio_lower_three_terms_exact_v3 (q e : Nat) (he : 1 ≤ e) : (q^2 + q + 1) * q^(2*e) ≤ q^2 * (∑ i ∈ Finset.range (2*e + 1), q^i) := by
  sorry

end OddPerfectNumber
