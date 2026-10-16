-- Prove2me | Theorems.Thm_LNChannels_SmallRate_csch_bounds
-- name    : LNChannels.SmallRate.csch_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:44.834982+00:00
-- url     : https://prove2.me/theorems/d7ca75ef-142a-42f2-8236-4e4d38c33f7e
-- title:
--   Hyperbolic cosecant bounds (22)
-- statement:
--   For every $x>0$, equation (22) bounds the squared hyperbolic cosecant on both sides:
--
--   $$\frac1{x^2}-\frac13<\frac1{\sinh^2x}<\frac1{x^2}.$$
--
--   These bounds control the diagonal channel cost. **Formalization Note** The strict positivity of $x$ avoids division by zero.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 11 (PDF 12), equation (22)

import Mathlib

set_option autoImplicit false

namespace LNChannels.SmallRate

/-- Inequalities (22) in the proof of Theorem 2(ii), p. 11. -/
theorem csch_bounds (x : ℝ) (hx : 0 < x) :
    1 / x ^ 2 - 1 / 3 < 1 / Real.sinh x ^ 2 ∧
      1 / Real.sinh x ^ 2 < 1 / x ^ 2 := by sorry

end LNChannels.SmallRate
