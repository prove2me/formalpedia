-- Prove2me | Theorems.Thm_MarketplaceLeakage_Benefits_optimum_values
-- name    : MarketplaceLeakage.Benefits.optimum_values
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:05.997923+00:00
-- url     : https://prove2.me/theorems/8b5870ea-e5e6-417e-accc-1b0124a63585
-- title:
--   Proof of Proposition 2, p. 37 — at the optimum, f*, p*_d and Π* in the three regimes μ ≤ 1/(2k), 1/(2k) ≤ μ ≤ μ̄, μ ≥ μ̄
-- statement:
--   In the leakage game with transaction benefit $b$ and $K(b) = \tfrac{k}{2}b^2$ (see the Setting), let $c < v$, $\mu > 0$, $k > 0$, and let $(b^*, f^*, p_d^*)$ be an optimum of the game. Then
--   $$
--   f^* = \begin{cases} b^* & \text{if } \mu \le \tfrac{1}{2k}, \\ \mu + \tfrac{b^*}{2} & \text{if } \tfrac{1}{2k} \le \mu \le \bar\mu, \\ v + b^* - c & \text{if } \mu \ge \bar\mu, \end{cases}
--   \qquad
--   p_d^* = \begin{cases} v & \text{if } \mu \le \tfrac{1}{2k}, \\ v - \dfrac{\mu(2k\mu - 1)}{4k\mu - 1} & \text{if } \tfrac{1}{2k} \le \mu \le \bar\mu, \\ \dfrac{v + c}{2} & \text{if } \mu \ge \bar\mu, \end{cases}
--   $$
--   and the marketplace's equilibrium profit is
--   $$
--   \Pi^* = \begin{cases} \dfrac{1}{2k} & \text{if } \mu \le \tfrac{1}{2k}, \\[6pt] \dfrac{\mu k}{2k - \frac{1}{2\mu}} & \text{if } \tfrac{1}{2k} \le \mu \le \bar\mu, \\[6pt] (v-c)\Bigl(1 - \dfrac{v-c}{2\mu}\Bigr) + \dfrac{1}{2k}\Bigl(1 - \dfrac{v-c}{2\mu}\Bigr)^2 & \text{if } \mu \ge \bar\mu, \end{cases}
--   $$
--   where $\bar\mu$ is the threshold of Proposition 2.
--
--   These are the equilibrium fee, direct price and profit that accompany the optimal investment $b^*$.
--
--   **Formalization Note** $f^*$ is expressed through the optimal $b^*$ of the same optimum, as on the page. The cases agree at the boundaries $\mu = 1/(2k)$ and $\mu = \bar\mu$; the Lean `if` takes the earlier case there.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 37, §8.3, Proof of Proposition 2 (displays for f*, p*_d, Π*)

import Mathlib
import Definitions.Def_MarketplaceLeakage_Benefits_Setting

namespace MarketplaceLeakage.Benefits

/-- Proof of Proposition 2, p. 37: at every optimum `(b*, f*, p*_d)` of the game, the fee, the
direct price and the marketplace's profit take the three-regime values
`f* = b*, μ + b*/2, v + b* − c`, `p*_d = v, v − μ(2kμ − 1)/(4kμ − 1), (v + c)/2` and
`Π* = 1/(2k), μk/(2k − 1/(2μ)), (v − c)(1 − (v − c)/(2μ)) + (1/(2k))(1 − (v − c)/(2μ))²`
for `μ ≤ 1/(2k)`, `1/(2k) ≤ μ ≤ μ̄` and `μ ≥ μ̄` respectively. -/
theorem optimum_values (v c μ k b f pd : ℝ) (hvc : c < v) (hμ : 0 < μ) (hk : 0 < k)
    (hopt : IsOpt v c μ k b f pd) :
    f = (if μ ≤ 1 / (2 * k) then b
         else if μ ≤ muBar v c k then μ + b / 2
         else v + b - c) ∧
    pd = (if μ ≤ 1 / (2 * k) then v
          else if μ ≤ muBar v c k then v - μ * (2 * k * μ - 1) / (4 * k * μ - 1)
          else (v + c) / 2) ∧
    MProfitB v μ k b f pd =
      (if μ ≤ 1 / (2 * k) then 1 / (2 * k)
       else if μ ≤ muBar v c k then μ * k / (2 * k - 1 / (2 * μ))
       else (v - c) * (1 - (v - c) / (2 * μ)) + 1 / (2 * k) * (1 - (v - c) / (2 * μ)) ^ 2) := by sorry

end MarketplaceLeakage.Benefits
