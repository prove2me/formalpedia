-- Prove2me | Theorems.Thm_InfoBargaining_SellerPayoff_optimalInfo_corner
-- name    : InfoBargaining.SellerPayoff.optimalInfo_corner
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:20:42.706021+00:00
-- url     : https://prove2.me/theorems/10665cec-d42a-4f51-ab2e-41d38f20a6c2
-- title:
--   Linear information cost gives a corner solution $\alpha^*\in\{\underline\alpha,\bar\alpha\}$
-- statement:
--   A seller and a buyer may trade one unit. Trade costs the seller $c>0$ and is worth $u$ to the buyer, who does not know $u$; the prior law of $u$ is $F$ with mean $\hat u>0$. Before negotiating, the buyer buys a truth-or-noise signal of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$; its posterior mean is $v=\alpha w+(1-\alpha)\hat u$, whose law is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$. The parties then split the net surplus $v-c$ in proportion to their bargaining powers $\theta_s,\theta_b\in(0,1)$, $\theta_s+\theta_b=1$.
--
--   Let $\mu$ be any probability law of the buyer's value with a finite mean, let $0<\underline\alpha<\bar\alpha<1$, $\bar k>0$, $\theta_b\in(0,1)$, $c\in\mathbb R$, and let the information cost be linear, $k(\alpha)=\bar k(\alpha-\underline\alpha)/(\bar\alpha-\underline\alpha)$. Then the buyer's optimal information acquisition
--
--   $$
--   \alpha^*\in\{\underline\alpha,\ \bar\alpha\}.
--   $$
--
--   Here $\alpha^*$ is the least maximizer of $U_b(\alpha)=\theta_bA(\alpha,c)-k(\alpha)$ on $[\underline\alpha,\bar\alpha]$. The buyer either acquires the minimum informativeness or pays $\bar k$ for the maximum.
--
--   Differences from the source:
--   - generalization: the four focal distributions, c ∈ (u̲, ū) → every probability law with a finite mean, every real c; reason: the argument uses only the convexity of A in α, which holds for every prior with a finite mean; the focal priors and admissible costs are instances
--   - reading: α∗, the solution to (6) → optimalInfo, the least maximizer of (6) on [α̲, ᾱ]; reason: (6) can have ties (uniform prior, c = 1/2: A(α, 1/2) = α/8); Corollary 1 sends every tie to α̲
--   - reading: θ_s, θ_b ∈ (0, 1), θ_s + θ_b = 1 (p. 7); [α̲, ᾱ] ⊆ (0, 1), k̄ = k(ᾱ) > 0 = k(α̲) (p. 8); c > 0 (p. 6), c ∈ (u̲, ū) (p. 7) → explicit hypotheses 0 < α̲ < ᾱ < 1, 0 < k̄, θ_b ∈ (0, 1) (c is any real, see the generalization above); reason: the section's standing assumptions; α̲ < ᾱ because k(α̲) = 0 < k̄ = k(ᾱ) and the linear k divides by ᾱ − α̲
--   - encoding: A(α, c) = ∫_c^v̄ (v − c) dG(v, α) with G(v, α) = F((v − (1 − α)û)/α) → totalSurplus μ α c = ∫ max(v − c, 0) d(postMeanLaw μ α), postMeanLaw the image of the prior under u ↦ αu + (1 − α)·priorMean μ; reason: the same quantity: G(·, α) is the CDF of that image law and (v − c)⁺ vanishes below c
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), proof of Corollary 1, unnumbered, p. 30

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_optimalInfo

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **With linear information cost the buyer's optimal informativeness is a corner.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022), proof of Corollary 1, p. 30: "This means that, given liner information-acquisition cost,
the optimal level of information acquisition must be corner solution, i.e., α∗ ∈ {α̲, ᾱ}."

For every probability prior `μ` with a finite mean, every `0 < α̲ < ᾱ < 1`, `k̄ > 0`,
`θ_b ∈ (0, 1)` and every real `c`, the least maximizer `α*` of (6) on `[α̲, ᾱ]` with
`k(α) = k̄(α − α̲)/(ᾱ − α̲)` is `α̲` or `ᾱ`.

**Formalization Note.** Stated for every integrable probability prior (generalization of "the
four focal distributions"); `α*` is the least maximizer (the tie-break of Corollary 1). -/
theorem optimalInfo_corner (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun u => u) μ) (αl αh kbar θb c : ℝ)
    (hαl : 0 < αl) (hαlh : αl < αh) (hαh : αh < 1) (hk : 0 < kbar)
    (hθb : θb ∈ Set.Ioo (0:ℝ) 1) :
    optimalInfo μ αl αh kbar θb c = αl ∨ optimalInfo μ αl αh kbar θb c = αh := by sorry

end InfoBargaining.SellerPayoff
