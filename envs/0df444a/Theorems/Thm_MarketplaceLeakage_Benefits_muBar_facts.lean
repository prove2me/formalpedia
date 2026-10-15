-- Prove2me | Theorems.Thm_MarketplaceLeakage_Benefits_muBar_facts
-- name    : MarketplaceLeakage.Benefits.muBar_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:07.532143+00:00
-- url     : https://prove2.me/theorems/01b0c94d-ed9d-4d1a-87f1-a0a2337512ca
-- title:
--   Proof of Proposition 2, pp. 36–37 — μ̄ > max{v − c, 1/(2k)}, and for μ > v − c the k-thresholds are equivalent to 1/(2k) ≤ μ ≤ μ̄ and μ ≥ μ̄
-- statement:
--   Let $c < v$ and $k > 0$, and let
--   $$
--   \bar\mu = \frac{v-c}{2} + \frac{1}{4k} + \sqrt{\Bigl(\frac{v-c}{2}\Bigr)^2 + \frac{1}{16k^2}} .
--   $$
--   Then $\bar\mu > \max\{v - c,\ 1/(2k)\}$, and for every $\mu > v - c$:
--   1. $\dfrac{1}{2\mu} \le k \le \dfrac{2\mu - (v-c)}{4\mu(\mu - (v-c))}$ if and only if $\dfrac{1}{2k} \le \mu \le \bar\mu$;
--   2. $k \ge \dfrac{2\mu - (v-c)}{4\mu(\mu - (v-c))}$ if and only if $\mu \ge \bar\mu$.
--
--   These equivalences translate the thresholds on the investment cost $k$ found for fixed $\mu$ into thresholds on the switching-cost scale $\mu$ for fixed $k$, which is the form in which Proposition 2 is stated.
--
--   **Formalization Note** The restriction $\mu > v - c$ is the paper's ("If $\mu > (v-c)$"); it keeps the denominator $4\mu(\mu - (v-c))$ positive.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), pp. 36–37, §8.3, Proof of Proposition 2 (definition of μ̄ and μ̄ > max{v − c, 1/(2k)})

import Mathlib
import Definitions.Def_MarketplaceLeakage_Benefits_Setting

namespace MarketplaceLeakage.Benefits

/-- Proof of Proposition 2, pp. 36–37: `μ̄ > max{v − c, 1/(2k)}`, and for `μ > v − c`,
`1/(2μ) ≤ k ≤ (2μ − (v − c))/(4μ(μ − (v − c)))` is equivalent to `1/(2k) ≤ μ ≤ μ̄`, while
`k ≥ (2μ − (v − c))/(4μ(μ − (v − c)))` is equivalent to `μ ≥ μ̄`. -/
theorem muBar_facts (v c k : ℝ) (hvc : c < v) (hk : 0 < k) :
    max (v - c) (1 / (2 * k)) < muBar v c k ∧
      ∀ μ : ℝ, v - c < μ →
        ((1 / (2 * μ) ≤ k ∧ k ≤ (2 * μ - (v - c)) / (4 * μ * (μ - (v - c)))) ↔
            (1 / (2 * k) ≤ μ ∧ μ ≤ muBar v c k)) ∧
        ((2 * μ - (v - c)) / (4 * μ * (μ - (v - c))) ≤ k ↔ muBar v c k ≤ μ) := by sorry

end MarketplaceLeakage.Benefits
