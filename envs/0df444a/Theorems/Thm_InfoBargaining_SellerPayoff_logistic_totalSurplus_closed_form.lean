-- Prove2me | Theorems.Thm_InfoBargaining_SellerPayoff_logistic_totalSurplus_closed_form
-- name    : InfoBargaining.SellerPayoff.logistic_totalSurplus_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:19:10.854594+00:00
-- url     : https://prove2.me/theorems/fe0d8606-99b2-458d-9053-ac402529b33c
-- title:
--   Logistic prior: $A(\alpha,c)=\alpha\ln[1+e^{(\hat u-c)/\alpha}]$
-- statement:
--   A seller and a buyer may trade one unit. Trade costs the seller $c>0$ and is worth $u$ to the buyer, who does not know $u$; the prior law of $u$ is $F$ with mean $\hat u>0$. Before negotiating, the buyer buys a truth-or-noise signal of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$; its posterior mean is $v=\alpha w+(1-\alpha)\hat u$, whose law is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$. The parties then split the net surplus $v-c$ in proportion to their bargaining powers $\theta_s,\theta_b\in(0,1)$, $\theta_s+\theta_b=1$.
--
--   For the logistic prior $F(u)=1/[1+e^{-(u-\hat u)}]$ on $\mathbb R$ with location $\hat u>0$ (and scale $1$), for every $\alpha\in(0,1)$ and every real $c$,
--
--   $$
--   A(\alpha,c)=\alpha\,\ln\!\big[1+e^{(\hat u-c)/\alpha}\big].
--   $$
--
--   The paper uses this formula to extend Corollary 1 to the logistic prior. The $\hat u$ of the formula is the location parameter, which is also the mean of the prior.
--
--   Differences from the source:
--   - generalization: c in the model's domain c ∈ (0, ∞) → every real c; reason: the closed form holds for every real c (the logistic prior has full support and the formula has a single branch, valid for every c); it specializes to the paper's range
--   - encoding: A(α, c) = ∫_c^v̄ (v − c) dG(v, α) with G(v, α) = F((v − (1 − α)û)/α) → totalSurplus μ α c = ∫ max(v − c, 0) d(postMeanLaw μ α), postMeanLaw the image of the prior under u ↦ αu + (1 − α)·priorMean μ; reason: the same quantity: G(·, α) is the CDF of that image law and (v − c)⁺ vanishes below c
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), proof of Corollary 1, unnumbered, p. 30

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_measure
import Definitions.Def_InfoBargaining_SellerPayoff_totalSurplus

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **Logistic prior: `A(α, c) = α ln[1 + e^{(û−c)/α}]`.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022), proof of Corollary 1, unnumbered, p. 30: "About the logistic prior
F(u) = 1/[1 + e^{−(u−û)}] for u ∈ (−∞, +∞), we have A(α, c) = α ln[1 + e^{(û−c)/α}]."

For every `û > 0`, every `α ∈ (0, 1)` and every real `c`.

**Formalization Note.** The `û` in the formula is the location parameter of the prior, which is
also its mean (symmetry); `postMeanLaw` uses the prior's mean. Stated for every real `c`
(generalization of the paper's `c > 0`). -/
theorem logistic_totalSurplus_closed_form (uhat : ℝ) (h : 0 < uhat) :
    ∀ α ∈ Set.Ioo (0:ℝ) 1, ∀ c : ℝ,
      totalSurplus (FocalPrior.logistic uhat h).measure α c =
        α * Real.log (1 + Real.exp ((uhat - c) / α)) := by sorry

end InfoBargaining.SellerPayoff
