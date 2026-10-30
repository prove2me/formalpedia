-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_eq_22_csch_sq_bounds
-- name    : LightningNetwork.RateBounds.eq_22_csch_sq_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:54:24.38418+00:00
-- url     : https://prove2.me/theorems/7eaef895-6a8b-4936-b1d3-ec1d3cecc6c5
-- title:
--   Eq. (22): $1/x^2 - 1/3 < \operatorname{csch}^2 x < 1/x^2$ for $x > 0$
-- statement:
--   For every $x > 0$,
--
--   $$
--   \frac1{x^2} - \frac13 \;<\; \operatorname{csch}^2 x \;<\; \frac1{x^2}.
--   $$
--
--   The lower bound turns (21) into the tractable lower bound (23).
--
--   Differences from the source:
--   - encoding: csch² x → 1 / sinh x ^ 2; reason: Mathlib has no csch; the arguments are positive, so sinh x ≠ 0 and the values agree
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), eq. (22), p. 11

import Mathlib

namespace LightningNetwork.RateBounds

/-- **The inequalities (22).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), eq. (22), p. 11: "To find a tractable lower bound, recall
the inequalities 1/x² − 1/3 < csch²x < 1/x², x > 0."

For every `x > 0`: `1/x² − 1/3 < csch² x < 1/x²`.

**Formalization Note.** `csch² x` is written `1 / sinh x ^ 2`. -/
theorem eq_22_csch_sq_bounds :
    ∀ x : ℝ, 0 < x →
      1 / x ^ 2 - 1 / 3 < 1 / Real.sinh x ^ 2 ∧ 1 / Real.sinh x ^ 2 < 1 / x ^ 2 := by sorry

end LightningNetwork.RateBounds
