-- Prove2me | Theorems.Thm_LNChannels_RateBounds_eq_22
-- name    : LNChannels.RateBounds.eq_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:48.669393+00:00
-- url     : https://prove2.me/theorems/4a0de265-e911-46ed-8641-b0ffa494236e
-- title:
--   Eq. (22), p. 11 — (21) in hyperbolic form, and $1/x^2-1/3<\operatorname{csch}^2x<1/x^2$ for $x>0$
-- statement:
--   1. **Hyperbolic form of (21).** For $\kappa>0$, $m>0$ and $B,C\in\mathbb R$, setting $\alpha=e^{\kappa}$,
--   $$2m+\frac{2B\alpha^{m}}{(\alpha^{m}-1)^2}-\frac{2C\alpha}{(\alpha-1)^2}=2m+\frac B2\operatorname{csch}^2\Big(\frac{\kappa m}2\Big)-\frac C2\operatorname{csch}^2\Big(\frac{\kappa}2\Big).$$
--   2. **Inequality (22).** For every $x>0$,
--   $$\frac1{x^2}-\frac13<\operatorname{csch}^2x<\frac1{x^2}.$$
--
--   Together they give the tractable lower bound (23) on the excess cost of a symmetric channel.
--
--   **Formalization Note** $\operatorname{csch}^2x$ is written $1/\sinh(x)^2$; $\alpha^m$ with real $m$ is a real power.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 11 (PDF p. 12), proof of Theorem 2(ii), display after (21) and eq. (22)

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

namespace LNChannels.RateBounds

/-- p. 11: with `α = e^κ` (`κ > 0`) and `m > 0`, (21) reads
`2m + (B/2)csch²(κm/2) − (C/2)csch²(κ/2)`; and inequality (22): `1/x² − 1/3 < csch² x < 1/x²`
for `x > 0`. -/
theorem eq_22 :
    (∀ κ B C m : ℝ, 0 < κ → 0 < m →
      2 * m + 2 * B * Real.exp κ ^ m / (Real.exp κ ^ m - 1) ^ 2
          - 2 * C * Real.exp κ / (Real.exp κ - 1) ^ 2 =
        2 * m + B / 2 / Real.sinh (κ * m / 2) ^ 2 - C / 2 / Real.sinh (κ / 2) ^ 2) ∧
    ∀ x : ℝ, 0 < x →
      1 / x ^ 2 - 1 / 3 < 1 / Real.sinh x ^ 2 ∧ 1 / Real.sinh x ^ 2 < 1 / x ^ 2 := by sorry

end LNChannels.RateBounds
