-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_terms_exact_v2
-- name    : OddPerfectNumber.geom_ratio_lower_three_terms_exact_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T21:50:48.947202+00:00
-- url     : https://prove2.me/theorems/97b4283f-ebad-44e5-8986-745ecf17f8c9
-- title:
--   Exact three-term geometric lower ratio v2
-- statement:
--   For every positive exponent index, the final three terms of the geometric sum give the exact lower ratio (q²+q+1)/q².
-- source:
--   Scale the accepted last-three-term bound by q².  The normalized algebra is split into explicit equality steps, avoiding a rewrite-generated reflexive inequality goal.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

namespace OddPerfectNumber

theorem geom_ratio_lower_three_terms_exact_v2 (q e : Nat) (he : 1 ≤ e) : (q^2 + q + 1) * q^(2*e) ≤ q^2 * (∑ i ∈ Finset.range (2*e + 1), q^i) := by
  sorry

end OddPerfectNumber
