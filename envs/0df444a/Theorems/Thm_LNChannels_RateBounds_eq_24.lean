-- Prove2me | Theorems.Thm_LNChannels_RateBounds_eq_24
-- name    : LNChannels.RateBounds.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:50.996483+00:00
-- url     : https://prove2.me/theorems/6fc51330-36d7-4c5f-a2fa-fa435a3b24d8
-- title:
--   Eq. (24), p. 12 — the lower bound (23) is minimized at $\hat m=(2B/\kappa^2)^{1/3}$ with value $3(2B/\kappa^2)^{1/3}-B/6-2C/\kappa^2$
-- statement:
--   Let $B>0$, $\kappa>0$, $C\in\mathbb R$, and consider the lower bound (23),
--   $$g(m)=2m+B\Big(\frac{2}{\kappa^2m^2}-\frac16\Big)-\frac{2C}{\kappa^2},\qquad m>0 .$$
--   Then $\hat m=(2B/\kappa^2)^{1/3}>0$ minimizes $g$ over $m>0$, and
--   $$g(\hat m)=3\Big(\frac{2B}{\kappa^2}\Big)^{1/3}-\frac B6-\frac{2C}{\kappa^2}.\tag{24}$$
--
--   Solving $g(\hat m)>0$ for $C$ gives the threshold $3(B\kappa^4/4)^{1/3}-(B/12)\kappa^2$ of Theorem 2(ii).
--
--   **Formalization Note** The cube root is the real power $(\cdot)^{1/3}$ of a positive number.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 12 (PDF p. 13), proof of Theorem 2(ii), eq. (24), for the function (23) of p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

namespace LNChannels.RateBounds

/-- (24), p. 12: for `B, κ > 0` the function (23), `2m + B(2/(κ²m²) − 1/6) − 2C/κ²`, attains its
minimum over `m > 0` at `m̂ = (2B/κ²)^{1/3}`, where it equals `3(2B/κ²)^{1/3} − B/6 − 2C/κ²`. -/
theorem eq_24 (B κ C : ℝ) (hB : 0 < B) (hκ : 0 < κ) :
    let g : ℝ → ℝ := fun m => 2 * m + B * (2 / (κ ^ 2 * m ^ 2) - 1 / 6) - 2 * C / κ ^ 2
    let mhat := (2 * B / κ ^ 2) ^ (1 / 3 : ℝ)
    0 < mhat ∧
      g mhat = 3 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ) - B / 6 - 2 * C / κ ^ 2 ∧
      ∀ m : ℝ, 0 < m → g mhat ≤ g m := by sorry

end LNChannels.RateBounds
