-- Prove2me | Theorems.Thm_MarketplaceLeakage_Benefits_best_response
-- name    : MarketplaceLeakage.Benefits.best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:01.210388+00:00
-- url     : https://prove2.me/theorems/99af0572-6a44-4f79-ab07-94eeb1c8db52
-- title:
--   Proof of Proposition 2, p. 34 — with benefit b the seller's optimal direct price is v − μ if f ≥ b + 2μ and v − (f − b)/2 if b ≤ f ≤ b + 2μ
-- statement:
--   In the leakage game with transaction benefit $b$ (see the Setting), let $c < v$, $\mu > 0$, and let the fee satisfy $f \ge b$. Then a direct price $p_d$ is seller-optimal at $(b,f)$ if and only if
--   $$
--   p_d = p_d^*(f) = \begin{cases} v - \mu & \text{if } f \ge b + 2\mu, \\[2pt] v - \tfrac12 (f - b) & \text{if } b \le f \le b + 2\mu. \end{cases}
--   $$
--   In particular the seller's optimal direct price exists and is unique. When $f = b$ the seller sets $p_d = v$ and there is no leakage; for $f > b$ the seller induces leakage, and above $b + 2\mu$ it diverts every buyer.
--
--   This is the first step of the proof of Proposition 2: it turns the marketplace's problem into an explicit optimization over $(b,f)$.
--
--   **Formalization Note** The two printed cases agree at $f = b + 2\mu$; the Lean `if` takes the first.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 34, §8.3, Proof of Proposition 2 (display for p*_d(f))

import Mathlib
import Definitions.Def_MarketplaceLeakage_Benefits_Setting

namespace MarketplaceLeakage.Benefits

/-- Proof of Proposition 2, p. 34: with uniform switching costs on `[0, μ]`, for every fee
`f ≥ b` the seller's profit-maximizing direct price is unique and equals `v − μ` if
`f ≥ b + 2μ` and `v − (f − b)/2` if `b ≤ f ≤ b + 2μ`. -/
theorem best_response (v c μ b f pd : ℝ) (hvc : c < v) (hμ : 0 < μ) (hbf : b ≤ f) :
    IsSOptB v c μ b f pd ↔ pd = (if b + 2 * μ ≤ f then v - μ else v - (f - b) / 2) := by sorry

end MarketplaceLeakage.Benefits
