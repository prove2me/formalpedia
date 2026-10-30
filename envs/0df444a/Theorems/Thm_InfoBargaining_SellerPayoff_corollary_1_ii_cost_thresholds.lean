-- Prove2me | Theorems.Thm_InfoBargaining_SellerPayoff_corollary_1_ii_cost_thresholds
-- name    : InfoBargaining.SellerPayoff.corollary_1_ii_cost_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:23:00.209351+00:00
-- url     : https://prove2.me/theorems/f91455c5-0dc3-4e6a-8cc6-a824b75f18e0
-- title:
--   Corollary 1 (ii): maximal information exactly for $c_l<c<c_h$, with $c_l\le\hat u\le c_h$
-- statement:
--   A seller and a buyer may trade one unit. Trade costs the seller $c>0$ and is worth $u$ to the buyer, who does not know $u$; the prior law of $u$ is $F$ with mean $\hat u>0$. Before negotiating, the buyer buys a truth-or-noise signal of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$; its posterior mean is $v=\alpha w+(1-\alpha)\hat u$, whose law is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$. The parties then split the net surplus $v-c$ in proportion to their bargaining powers $\theta_s,\theta_b\in(0,1)$, $\theta_s+\theta_b=1$.
--
--   Let $P$ be any of the four focal priors with mean $\hat u$, $0<\underline\alpha<\bar\alpha<1$, $\bar k>0$, $\theta_b\in(0,1)$, the cost linear. There are $c_l\le\hat u$ and $c_h\ge\hat u$ such that for every admissible cost $c$
--
--   $$
--   \alpha^*=\begin{cases}\bar\alpha, & c_l<c<c_h,\\ \underline\alpha, & c\le c_l\ \text{or}\ c\ge c_h.\end{cases}
--   $$
--
--   The buyer gathers maximal information only when the seller's cost is intermediate, close to the prior mean, where knowing the value matters most for the trade decision.
--
--   Differences from the source:
--   - reading: α∗, the solution to (6) → optimalInfo, the least maximizer of (6) on [α̲, ᾱ]; reason: (6) can have ties (uniform prior, c = 1/2: A(α, 1/2) = α/8); Corollary 1 sends every tie to α̲
--   - reading: θ_s, θ_b ∈ (0, 1), θ_s + θ_b = 1 (p. 7); [α̲, ᾱ] ⊆ (0, 1), k̄ = k(ᾱ) > 0 = k(α̲) (p. 8); c > 0 (p. 6), c ∈ (u̲, ū) (p. 7) → explicit hypotheses 0 < α̲ < ᾱ < 1, 0 < k̄, θ ∈ (0, 1), c ∈ P.costDomain, θ_b = 1 − θ_s; reason: the section's standing assumptions; α̲ < ᾱ because k(α̲) = 0 < k̄ = k(ᾱ) and the linear k divides by ᾱ − α̲
--   - encoding: A(α, c) = ∫_c^v̄ (v − c) dG(v, α) with G(v, α) = F((v − (1 − α)û)/α) → totalSurplus μ α c = ∫ max(v − c, 0) d(postMeanLaw μ α), postMeanLaw the image of the prior under u ↦ αu + (1 − α)·priorMean μ; reason: the same quantity: G(·, α) is the CDF of that image law and (v − c)⁺ vanishes below c
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), Corollary 1 (ii), p. 13

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_measure
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_costDomain
import Definitions.Def_InfoBargaining_SellerPayoff_optimalInfo

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **Corollary 1 (ii): maximal information exactly for intermediate costs `c_l < c < c_h`.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022), Corollary 1 (ii), p. 13: "(ii) There exist c_l ≤ û and c_h ≥ û such that the optimal level
of buyer information acquisition is: α∗ = α̲ for c ≤ c_l or c ≥ c_h, and α∗ = ᾱ for
c_l < c < c_h."

For every focal prior, every `0 < α̲ < ᾱ < 1`, `k̄ > 0` and `θ_b ∈ (0, 1)` there are
`c_l ≤ û ≤ c_h` (`û` the prior mean) such that for every admissible cost `c`, `α* = ᾱ` if
`c_l < c < c_h` and `α* = α̲` otherwise.

**Formalization Note.** `û` is `priorMean P.measure`; `α*` is the least maximizer of (6);
`c` ranges over `P.costDomain` (`c > 0` and inside the support, pp. 6–7). -/
theorem corollary_1_ii_cost_thresholds (P : FocalPrior) (αl αh kbar θb : ℝ)
    (hαl : 0 < αl) (hαlh : αl < αh) (hαh : αh < 1) (hk : 0 < kbar)
    (hθb : θb ∈ Set.Ioo (0:ℝ) 1) :
    ∃ cl ch : ℝ, cl ≤ priorMean P.measure ∧ priorMean P.measure ≤ ch ∧
      ∀ c ∈ P.costDomain,
        optimalInfo P.measure αl αh kbar θb c = if cl < c ∧ c < ch then αh else αl := by sorry

end InfoBargaining.SellerPayoff
