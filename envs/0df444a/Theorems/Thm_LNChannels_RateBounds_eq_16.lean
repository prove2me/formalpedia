-- Prove2me | Theorems.Thm_LNChannels_RateBounds_eq_16
-- name    : LNChannels.RateBounds.eq_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:24.304462+00:00
-- url     : https://prove2.me/theorems/92fdba1a-0fe1-4b6c-9309-a5b32e3b681f
-- title:
--   Eq. (16), p. 11 — $2B/(B\kappa+\sqrt{B\kappa(B\kappa+4)})\ge\alpha/\kappa$ for $\kappa\ge\alpha^2/(B(1-\alpha))$
-- statement:
--   Let $B>0$, $\kappa>0$ and $0<\alpha<1$. If $\kappa\ge \alpha^2/(B(1-\alpha))$, then
--   $$\frac{2B}{B\kappa+\sqrt{B\kappa(B\kappa+4)}}\ \ge\ \frac{\alpha}{\kappa}.$$
--
--   The left side is the term $B/(e^{\kappa\hat m}-1)$ of the minimal value $F(\hat m)$; the inequality is the first step of the lower bound (17) on $F(\hat m)$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 11 (PDF p. 12), proof of Theorem 2(i), eq. (16)

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

namespace LNChannels.RateBounds

/-- Inequality (16), p. 11: `2B/(Bκ + √(Bκ(Bκ + 4))) ≥ α/κ` for `κ ≥ α²/(B(1 − α))`, `0 < α < 1`. -/
theorem eq_16 (B κ α : ℝ) (hB : 0 < B) (hκ : 0 < κ) (hα0 : 0 < α) (hα1 : α < 1)
    (hκα : α ^ 2 / (B * (1 - α)) ≤ κ) :
    α / κ ≤ 2 * B / (B * κ + √(B * κ * (B * κ + 4))) := by sorry

end LNChannels.RateBounds
