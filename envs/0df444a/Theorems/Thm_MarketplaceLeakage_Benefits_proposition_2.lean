-- Prove2me | Theorems.Thm_MarketplaceLeakage_Benefits_proposition_2
-- name    : MarketplaceLeakage.Benefits.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:09.100459+00:00
-- url     : https://prove2.me/theorems/59c3b9cd-f1ec-4df3-8133-3f50446a94ae
-- title:
--   Proposition 2, p. 12 — the optimal transaction benefit b* decreases in k and is constant, then decreasing, then increasing in μ; leakage is zero, then increasing, then decreasing
-- statement:
--   Consider the leakage game with transaction benefits (see the Setting): switching costs are uniform on $[0,\mu]$, $\mu > 0$, the marketplace invests $K(b) = \tfrac{k}{2}b^2$ with $k > 0$ in a benefit $b \ge 0$ and charges a fee $b \le f \le v - c + b$, and the seller ($c < v$) answers with a profit-maximizing direct price $p_d \le v$. Let
--   $$
--   \bar\mu = \frac{v-c}{2} + \frac{1}{4k} + \sqrt{\Bigl(\frac{v-c}{2}\Bigr)^2 + \frac{1}{16k^2}} .
--   $$
--   Then:
--   1. An optimum $(b^*, f^*, p_d^*)$ exists, and at every optimum the marketplace's optimal choice of transaction benefits is
--   $$
--   b^* = \begin{cases} \dfrac{1}{k} & \text{if } \mu \le \tfrac{1}{2k}, \\[6pt] \dfrac{1}{2k - \frac{1}{2\mu}} & \text{if } \tfrac{1}{2k} \le \mu \le \bar\mu, \\[6pt] \dfrac{1}{k} - \dfrac{v-c}{2k\mu} & \text{if } \mu \ge \bar\mu. \end{cases}
--   $$
--   2. $b^*$ is strictly decreasing in the investment cost $k$: for fixed $\mu$ and $k_1 < k_2$, every optimal investment at $k_2$ is strictly smaller than every optimal investment at $k_1$.
--   3. For fixed $k$, as a function of the switching-cost scale $\mu$: for $\mu \le 1/(2k)$ the optimal investment is constant at $1/k$ and the equilibrium leakage $G(v - p_d^*)$ is zero; on $[1/(2k), \bar\mu]$ the optimal investment is strictly decreasing and the leakage strictly increasing in $\mu$; on $[\bar\mu, \infty)$ the optimal investment is strictly increasing and the leakage strictly decreasing in $\mu$.
--
--   The proposition shows that the marketplace's investment in fighting leakage is non-monotone in switching costs: with low switching costs it buys out leakage entirely; with intermediate ones it tolerates growing leakage and invests less; with high ones it again invests more as leakage falls.
--
--   **Formalization Note** "Optimal" means an optimum of the joint problem over $(b,f)$ with the seller best-responding (`IsOpt`); no closed form for $b^*$ is defined. The comparative statics compare optimal choices at two parameter values. "Decreasing" and "increasing" are read strictly, as on the page. The cases of $b^*$ agree at $\mu = 1/(2k)$ and $\mu = \bar\mu$, so the boundary convention of the Lean `if` is immaterial.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 12, Proposition 2

import Mathlib
import Definitions.Def_MarketplaceLeakage_Benefits_Setting

namespace MarketplaceLeakage.Benefits

/-- Proposition 2, p. 12: with uniform switching costs on `[0, μ]` and `K(b) = (k/2) b²`, `k > 0`,
the marketplace's optimal transaction benefit is `b* = 1/k` for `μ ≤ 1/(2k)`,
`1/(2k − 1/(2μ))` for `1/(2k) ≤ μ ≤ μ̄` and `1/k − (v − c)/(2kμ)` for `μ ≥ μ̄`; `b*` is
strictly decreasing in `k`; in `μ` it is constant, then strictly decreasing on `[1/(2k), μ̄]`,
then strictly increasing on `[μ̄, ∞)`; the equilibrium leakage is zero, then strictly increasing
on `[1/(2k), μ̄]`, then strictly decreasing on `[μ̄, ∞)`. -/
theorem proposition_2 (v c : ℝ) (hvc : c < v) :
    -- the optimal investment b*: an optimum exists, and every optimum has b = b*
    (∀ μ k : ℝ, 0 < μ → 0 < k →
      (∃ b f pd : ℝ, IsOpt v c μ k b f pd) ∧
      ∀ b f pd : ℝ, IsOpt v c μ k b f pd →
        b = (if μ ≤ 1 / (2 * k) then 1 / k
             else if μ ≤ muBar v c k then 1 / (2 * k - 1 / (2 * μ))
             else 1 / k - (v - c) / (2 * k * μ))) ∧
    -- b* is strictly decreasing in the investment cost k
    (∀ μ k₁ k₂ : ℝ, 0 < μ → 0 < k₁ → k₁ < k₂ → ∀ b₁ f₁ p₁ b₂ f₂ p₂ : ℝ,
      IsOpt v c μ k₁ b₁ f₁ p₁ → IsOpt v c μ k₂ b₂ f₂ p₂ → b₂ < b₁) ∧
    -- dependence of b* and of the MarketplaceLeakage.Baseline.leakage on μ, for fixed k
    (∀ k : ℝ, 0 < k →
      (∀ μ : ℝ, 0 < μ → μ ≤ 1 / (2 * k) → ∀ b f pd : ℝ, IsOpt v c μ k b f pd →
        b = 1 / k ∧ MarketplaceLeakage.Baseline.leakage v μ pd = 0) ∧
      (∀ μ₁ μ₂ : ℝ, 1 / (2 * k) ≤ μ₁ → μ₁ < μ₂ → μ₂ ≤ muBar v c k →
        ∀ b₁ f₁ p₁ b₂ f₂ p₂ : ℝ, IsOpt v c μ₁ k b₁ f₁ p₁ → IsOpt v c μ₂ k b₂ f₂ p₂ →
          b₂ < b₁ ∧ MarketplaceLeakage.Baseline.leakage v μ₁ p₁ < MarketplaceLeakage.Baseline.leakage v μ₂ p₂) ∧
      (∀ μ₁ μ₂ : ℝ, muBar v c k ≤ μ₁ → μ₁ < μ₂ →
        ∀ b₁ f₁ p₁ b₂ f₂ p₂ : ℝ, IsOpt v c μ₁ k b₁ f₁ p₁ → IsOpt v c μ₂ k b₂ f₂ p₂ →
          b₁ < b₂ ∧ MarketplaceLeakage.Baseline.leakage v μ₂ p₂ < MarketplaceLeakage.Baseline.leakage v μ₁ p₁)) := by sorry

end MarketplaceLeakage.Benefits
