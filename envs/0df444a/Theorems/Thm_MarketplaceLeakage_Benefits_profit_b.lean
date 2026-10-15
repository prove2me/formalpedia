-- Prove2me | Theorems.Thm_MarketplaceLeakage_Benefits_profit_b
-- name    : MarketplaceLeakage.Benefits.profit_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:08.03656+00:00
-- url     : https://prove2.me/theorems/49bf1f96-677e-41be-9b5a-bb35a0ad788c
-- title:
--   Proof of Proposition 2, p. 35 — for fixed b the marketplace's best profit Π(b) has three regimes with breakpoints max{2μ − 2(v − c), 0} and 2μ
-- statement:
--   In the leakage game with transaction benefit $b$ (see the Setting), let $c < v$, $\mu > 0$ and $b \ge 0$. Over all fees $b \le f \le v - c + b$, with the seller answering by a seller-optimal direct price, the marketplace's profit attains its maximum, and the maximum is
--   $$
--   \Pi(b) = \begin{cases} b - \dfrac{kb^2}{2} & \text{if } b \ge 2\mu, \\[6pt] \dfrac{(2\mu + b)^2}{8\mu} - \dfrac{kb^2}{2} & \text{if } \max\{2\mu - 2(v-c), 0\} \le b \le 2\mu, \\[6pt] (v - c + b)\Bigl(1 - \dfrac{v-c}{2\mu}\Bigr) - \dfrac{kb^2}{2} & \text{if } 0 \le b \le 2\mu - 2(v-c). \end{cases}
--   $$
--   The three regimes correspond to the optimal fee $f = b$ (no leakage), the interior fee $f = \mu + b/2$, and the corner fee $f = v - c + b$.
--
--   This reduces the marketplace's joint choice of $(b,f)$ to a one-dimensional problem in $b$.
--
--   **Formalization Note** The paper writes the third case as $0 \le b \le \max\{2\mu - 2(v-c), 0\}$. When $\mu < v - c$ that range is the single point $b = 0$, where it overlaps the second case and gives a different (wrong) value: at $b = 0$, $v - c = 2$, $\mu = 1$ the true maximum is $\mu/2 = 1/2$ (fee $f = \mu$), while the third line gives $0$. The statement therefore uses the third line only for $b \le 2\mu - 2(v-c)$, which is the paper's case when $2\mu - 2(v-c) \ge 0$. "Max" is stated as `IsGreatest` (the value is attained). On overlapping boundaries the lines agree.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 35, §8.3, Proof of Proposition 2 (display for Π(b))

import Mathlib
import Definitions.Def_MarketplaceLeakage_Benefits_Setting

namespace MarketplaceLeakage.Benefits

/-- Proof of Proposition 2, p. 35: for a fixed benefit `b ≥ 0`, the largest profit the
marketplace can obtain over the fees `b ≤ f ≤ v − c + b` (with the seller answering optimally) is
`Π(b) = b − kb²/2` if `b ≥ 2μ`, `(2μ + b)²/(8μ) − kb²/2` if `max{2μ − 2(v − c), 0} ≤ b ≤ 2μ`,
and `(v − c + b)(1 − (v − c)/(2μ)) − kb²/2` if `0 ≤ b ≤ 2μ − 2(v − c)`; the maximum is attained. -/
theorem profit_b (v c μ k b : ℝ) (hvc : c < v) (hμ : 0 < μ) (hb : 0 ≤ b) :
    IsGreatest
      {π : ℝ | ∃ f pd : ℝ, b ≤ f ∧ f ≤ v - c + b ∧ IsSOptB v c μ b f pd ∧
        π = MProfitB v μ k b f pd}
      (if 2 * μ ≤ b then b - k * b ^ 2 / 2
       else if b ≤ 2 * μ - 2 * (v - c) then
         (v - c + b) * (1 - (v - c) / (2 * μ)) - k * b ^ 2 / 2
       else (2 * μ + b) ^ 2 / (8 * μ) - k * b ^ 2 / 2) := by sorry

end MarketplaceLeakage.Benefits
