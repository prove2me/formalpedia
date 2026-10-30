-- Prove2me | Theorems.Thm_InfoBargaining_SellerPayoff_totalSurplus_monotone_convex
-- name    : InfoBargaining.SellerPayoff.totalSurplus_monotone_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:19:54.25854+00:00
-- url     : https://prove2.me/theorems/3de9b299-7b43-4f9f-a63d-1f6e97e65b0d
-- title:
--   $A(\alpha,c)$ is nondecreasing and convex in $\alpha$
-- statement:
--   A seller and a buyer may trade one unit. Trade costs the seller $c>0$ and is worth $u$ to the buyer, who does not know $u$; the prior law of $u$ is $F$ with mean $\hat u>0$. Before negotiating, the buyer buys a truth-or-noise signal of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$; its posterior mean is $v=\alpha w+(1-\alpha)\hat u$, whose law is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$. The parties then split the net surplus $v-c$ in proportion to their bargaining powers $\theta_s,\theta_b\in(0,1)$, $\theta_s+\theta_b=1$.
--
--   Let $\mu$ be any probability law of the buyer's value with a finite mean, and $c$ any real number. Then the total ex ante surplus
--
--   $$
--   \alpha\ \longmapsto\ A(\alpha,c)=\int\max\{v-c,0\}\,dG(v,\alpha)
--   $$
--
--   is nondecreasing and convex on $[0,1]$.
--
--   Convexity is what makes the buyer's optimal information acquisition a corner solution under a linear cost; monotonicity says that a more informative signal never shrinks the total pie.
--
--   Differences from the source:
--   - generalization: the four focal distributions, α ∈ (0, 1) → every probability law with a finite mean, α ∈ [0, 1]; reason: the argument (convexity of α ↦ (α(u − û) + û − c)⁺ and Jensen at α = 0) uses only a finite mean; the focal priors are instances
--   - reading: A(α, c) is increasing in α → MonotoneOn (nondecreasing); reason: the paper's own uniform example has A constant for α ≤ |1 − 2c| (p. 30), so increasing is meant weakly
--   - encoding: A(α, c) = ∫_c^v̄ (v − c) dG(v, α) with G(v, α) = F((v − (1 − α)û)/α) → totalSurplus μ α c = ∫ max(v − c, 0) d(postMeanLaw μ α), postMeanLaw the image of the prior under u ↦ αu + (1 − α)·priorMean μ; reason: the same quantity: G(·, α) is the CDF of that image law and (v − c)⁺ vanishes below c
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §3.2, p. 13 ("the ex ante surplus A(α, c) is convex in α"); proof of Corollary 1, p. 30 ("A(α, c) is increasing and convex in α")

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_totalSurplus

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **The total ex ante surplus `A(α, c)` is nondecreasing and convex in `α`.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022), §3.2, p. 13: "For the distributions we consider, the ex ante surplus A(α, c) is convex in
α."; proof of Corollary 1, p. 30: "For each of these cases, we can verify that A(α, c) is
increasing and convex in α".

For every probability measure `μ` on `ℝ` with a finite mean and every real `c`, the map
`α ↦ A(α, c)` is monotone and convex on `[0, 1]`.

**Formalization Note.** Stated for every integrable probability prior, of which the four focal
priors are instances (generalization). "Increasing" is weak: for the uniform prior `A` is
constant for `α ≤ |1 − 2c|` (p. 30). -/
theorem totalSurplus_monotone_convex (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun u => u) μ) (c : ℝ) :
    MonotoneOn (fun α => totalSurplus μ α c) (Set.Icc 0 1) ∧
      ConvexOn ℝ (Set.Icc 0 1) (fun α => totalSurplus μ α c) := by sorry

end InfoBargaining.SellerPayoff
