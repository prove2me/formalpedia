-- Prove2me | Theorems.Thm_MarketplaceLeakage_Benefits_profit_b_f
-- name    : MarketplaceLeakage.Benefits.profit_b_f
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:07.260063+00:00
-- url     : https://prove2.me/theorems/4c52c1db-71c2-4743-b56b-0d856291236d
-- title:
--   Proof of Proposition 2, p. 34 — the marketplace's profit Π(b, f) is −kb²/2 if f ≥ b + 2μ and f(1 − (f − b)/(2μ)) − kb²/2 if b ≤ f ≤ b + 2μ
-- statement:
--   In the leakage game with transaction benefit $b$ and investment cost $K(b) = \tfrac{k}{2}b^2$ (see the Setting), let $c < v$, $\mu > 0$, $f \ge b$, and let $p_d$ be seller-optimal at $(b,f)$. Then the marketplace's profit is
--   $$
--   \Pi(b,f) = \begin{cases} -\dfrac{kb^2}{2} & \text{if } f \ge b + 2\mu, \\[6pt] f\Bigl(1 - \dfrac{1}{2\mu}(f-b)\Bigr) - \dfrac{kb^2}{2} & \text{if } b \le f \le b + 2\mu. \end{cases}
--   $$
--
--   The marketplace's overall value is the maximum of $\Pi(b,f)$ over $b \ge 0$, $b \le f \le v - c + b$; this formula is what that maximization works with.
--
--   **Formalization Note** The paper's display has a third line, $\Pi(b,f) = b - kb^2/2$ if $f = b$. It is the second line evaluated at $f = b$, so the two-line form states the same function. The two lines agree at $f = b + 2\mu$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 34, §8.3, Proof of Proposition 2 (display for Π(b, f))

import Mathlib
import Definitions.Def_MarketplaceLeakage_Benefits_Setting

namespace MarketplaceLeakage.Benefits

/-- Proof of Proposition 2, p. 34: at benefit `b` and fee `f ≥ b`, when the seller answers
optimally, the marketplace's profit is `Π(b, f) = −kb²/2` if `f ≥ b + 2μ` and
`f (1 − (f − b)/(2μ)) − kb²/2` if `b ≤ f ≤ b + 2μ` (the printed third line, `b − kb²/2` at
`f = b`, is the second line at `f = b`). -/
theorem profit_b_f (v c μ k b f pd : ℝ) (hvc : c < v) (hμ : 0 < μ) (hbf : b ≤ f)
    (hS : IsSOptB v c μ b f pd) :
    MProfitB v μ k b f pd =
      (if b + 2 * μ ≤ f then -(k * b ^ 2 / 2)
       else f * (1 - (f - b) / (2 * μ)) - k * b ^ 2 / 2) := by sorry

end MarketplaceLeakage.Benefits
