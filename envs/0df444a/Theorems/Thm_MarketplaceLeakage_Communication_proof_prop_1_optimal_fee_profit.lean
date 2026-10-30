-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_proof_prop_1_optimal_fee_profit
-- name    : MarketplaceLeakage.Communication.proof_prop_1_optimal_fee_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:06:51.922238+00:00
-- url     : https://prove2.me/theorems/46aa8564-e73b-4571-aa01-db4171092478
-- title:
--   Proof of Proposition 1: $f^*=\min\{\mu,v-c\}$ and $\Pi^*(\mu)$ of (6)
-- statement:
--   Let $\mu>0$ and $c<v$, and let $\Pi(f)$ be the marketplace's profit (5) with uniform switching costs $G(s)=s/\mu$. Then:
--
--   1. $\mu$ is the unique maximizer of $f\left(1-\frac{f}{2\mu}\right)$ over all real $f$, and $\mu<2\mu$;
--   2. over the fees $f\le v-c$, $\Pi(f)$ attains its maximum exactly at $f^*=\min\{\mu,v-c\}$, and the maximum is
--
--   $$
--   \Pi^*(\mu)=\begin{cases}\dfrac{\mu}{2} & \text{if } \mu\le v-c,\\ (v-c)\left(1-\dfrac{v-c}{2\mu}\right) & \text{if } \mu\ge v-c.\end{cases}
--   $$
--
--   This identifies $\Pi^*(\mu)$ of (6) as the marketplace's optimal profit, the instance of $\Pi^*$ used in the last clause of Proposition 3.
--
--   Differences from the source:
--
--   - reading: "M solves arg max_f f(1 − f/(2µ)) = µ" → µ is the unique maximizer of f(1 − f/(2µ)) over all real f; reason: arg max read as the unique maximizer
--   - encoding: M's profit (5) derived from S's pricing (4) → (5) taken as the definition uniformFeeProfit; reason: the proof works from (5); the switching-cost game is not formalized
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §8.2 (proof of Proposition 1), unnumbered, p. 34; Proposition 1, display (6), p. 10

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_uniformFeeProfit
import Definitions.Def_MarketplaceLeakage_Communication_piStarUniform

namespace MarketplaceLeakage.Communication

/-- **Proof of Proposition 1: `f* = min{µ, v − c}` and `Π*(µ)` of (6).**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §8.2 (proof of Proposition 1), unnumbered, p. 34: "Given (5) and noting second-order
conditions hold for any f > 0 and µ > 0, we have that M solves
arg max_f f (1 − f/(2µ)) = µ < 2µ. Taking into account that f ≤ v − c, this implies the
level of f∗ and Π∗ given in Proposition 1." Proposition 1, display (6), p. 10:
"f∗ (µ) = min {µ, v − c}" and "Π∗ (µ) = µ/2 if µ ≤ v − c ; (v − c)(1 − (v−c)/(2µ)) if
µ ≥ v − c".

For `µ > 0` and `c < v`:
(1) `µ` is the unique maximizer of `f (1 − f/(2µ))` over all real `f`, and `µ < 2µ`;
(2) over fees `f ≤ v − c`, the profit (5) attains its maximum `Π*(µ)` exactly at
`f* = min{µ, v − c}`.

**Formalization Note.** (5) is `uniformFeeProfit` and (6) is `piStarUniform`. "M will
always set f ≤ v − c" (p. 9) is the feasible set `Set.Iic (v − c)`. -/
theorem proof_prop_1_optimal_fee_profit {v c μ : ℝ} (hμ : 0 < μ) (hcv : c < v) :
    ((∀ f : ℝ, f * (1 - f / (2 * μ)) ≤ μ * (1 - μ / (2 * μ))) ∧
        (∀ f : ℝ, f * (1 - f / (2 * μ)) = μ * (1 - μ / (2 * μ)) → f = μ) ∧ μ < 2 * μ) ∧
      IsGreatest (uniformFeeProfit μ '' Set.Iic (v - c)) (piStarUniform v c μ) ∧
      uniformFeeProfit μ (min μ (v - c)) = piStarUniform v c μ ∧
      ∀ f : ℝ, f ≤ v - c → uniformFeeProfit μ f = piStarUniform v c μ → f = min μ (v - c) := by sorry

end MarketplaceLeakage.Communication
