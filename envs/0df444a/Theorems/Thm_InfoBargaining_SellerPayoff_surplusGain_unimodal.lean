-- Prove2me | Theorems.Thm_InfoBargaining_SellerPayoff_surplusGain_unimodal
-- name    : InfoBargaining.SellerPayoff.surplusGain_unimodal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:21:07.586159+00:00
-- url     : https://prove2.me/theorems/3a5f11a2-093c-4803-8641-511955f91ecf
-- title:
--   $A(\bar\alpha,c)-A(\underline\alpha,c)$ rises in $c$ up to $\hat u$ and falls after
-- statement:
--   A seller and a buyer may trade one unit. Trade costs the seller $c>0$ and is worth $u$ to the buyer, who does not know $u$; the prior law of $u$ is $F$ with mean $\hat u>0$. Before negotiating, the buyer buys a truth-or-noise signal of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$; its posterior mean is $v=\alpha w+(1-\alpha)\hat u$, whose law is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$. The parties then split the net surplus $v-c$ in proportion to their bargaining powers $\theta_s,\theta_b\in(0,1)$, $\theta_s+\theta_b=1$.
--
--   Let $\mu$ be any probability law of the buyer's value with a finite mean $\hat u$, and let $0\le\underline\alpha\le\bar\alpha\le1$. Then the value of more information
--
--   $$
--   \Delta A(c)=A(\bar\alpha,c)-A(\underline\alpha,c)
--   $$
--
--   is nondecreasing in $c$ on $(-\infty,\hat u]$ and nonincreasing on $[\hat u,\infty)$; its peak is at the prior mean.
--
--   This unimodality, which comes from the rotation of $G(\cdot,\alpha)$ around $\hat u$ (display (1)), is what makes the set of costs at which the buyer acquires maximal information an interval around $\hat u$ (Corollary 1 (ii)).
--
--   Differences from the source:
--   - generalization: the four focal distributions, 0 < α̲ < ᾱ < 1 → every probability law with a finite mean, 0 ≤ α̲ ≤ ᾱ ≤ 1, every real c; reason: the argument uses only the rotation of G around û, valid for every prior with a finite mean; the paper's case is an instance
--   - reading: first increases and then decreases in c, peak at û → MonotoneOn on (−∞, û] and AntitoneOn on [û, ∞); reason: weak: for the uniform prior ΔA = 0 near both ends of the support (p. 30)
--   - encoding: A(α, c) = ∫_c^v̄ (v − c) dG(v, α) with G(v, α) = F((v − (1 − α)û)/α) → totalSurplus μ α c = ∫ max(v − c, 0) d(postMeanLaw μ α), postMeanLaw the image of the prior under u ↦ αu + (1 − α)·priorMean μ; reason: the same quantity: G(·, α) is the CDF of that image law and (v − c)⁺ vanishes below c
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), proof of Corollary 1, unnumbered, p. 30 ("A(ᾱ, c) − A(α̲, c) first increases and then decreases in c"; "reaches the peak at û")

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_totalSurplus

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **The value of more information, `A(ᾱ, c) − A(α̲, c)`, rises in `c` up to `û` and falls after.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022), proof of Corollary 1, p. 30: "Note also that A(ᾱ, c) − A(α̲, c) first increases and then
decreases in c."; and "the derivative of A(α, c) with respect to α first increases and then
decreases in c and reaches the peak at û."

For every probability prior `μ` with a finite mean `û = priorMean μ` and every
`0 ≤ α̲ ≤ ᾱ ≤ 1`, the map `c ↦ A(ᾱ, c) − A(α̲, c)` is monotone on `(−∞, û]` and antitone on
`[û, ∞)`.

**Formalization Note.** Stated for every integrable probability prior and every
`0 ≤ α̲ ≤ ᾱ ≤ 1` (generalization). Weak monotonicity: for the uniform prior the difference is
`0` near both ends of the support (p. 30). -/
theorem surplusGain_unimodal (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun u => u) μ) (αl αh : ℝ)
    (hαl : 0 ≤ αl) (hαlh : αl ≤ αh) (hαh : αh ≤ 1) :
    MonotoneOn (fun c => totalSurplus μ αh c - totalSurplus μ αl c) (Set.Iic (priorMean μ)) ∧
      AntitoneOn (fun c => totalSurplus μ αh c - totalSurplus μ αl c)
        (Set.Ici (priorMean μ)) := by sorry

end InfoBargaining.SellerPayoff
