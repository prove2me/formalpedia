-- Prove2me | Theorems.Thm_InfoBargaining_SellerPayoff_exponential_totalSurplus_closed_form
-- name    : InfoBargaining.SellerPayoff.exponential_totalSurplus_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:18:35.444395+00:00
-- url     : https://prove2.me/theorems/ed90af7b-1e38-414a-b559-e8278ad97a58
-- title:
--   Exponential prior: closed form of $A(\alpha,c)$
-- statement:
--   A seller and a buyer may trade one unit. Trade costs the seller $c>0$ and is worth $u$ to the buyer, who does not know $u$; the prior law of $u$ is $F$ with mean $\hat u>0$. Before negotiating, the buyer buys a truth-or-noise signal of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$; its posterior mean is $v=\alpha w+(1-\alpha)\hat u$, whose law is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$. The parties then split the net surplus $v-c$ in proportion to their bargaining powers $\theta_s,\theta_b\in(0,1)$, $\theta_s+\theta_b=1$.
--
--   For the exponential prior $F(u)=1-e^{-u/\hat u}$, $u\ge0$, with mean $\hat u>0$, for every $\alpha\in(0,1)$ and every real $c$,
--
--   $$
--   A(\alpha,c)=\begin{cases}\hat u-c, & \alpha\le 1-c/\hat u,\\[4pt] \alpha\hat u\,e^{((1-\alpha)\hat u-c)/(\alpha\hat u)}, & \alpha\ge 1-c/\hat u.\end{cases}
--   $$
--
--   The two branches agree at $\alpha=1-c/\hat u$. The paper uses this formula to extend Corollary 1 to the exponential prior.
--
--   Differences from the source:
--   - generalization: c in the model's domain c ∈ (0, ∞) → every real c; reason: the closed form holds for every real c (outside the support only the first branch applies); it specializes to the paper's range
--   - encoding: A(α, c) = ∫_c^v̄ (v − c) dG(v, α) with G(v, α) = F((v − (1 − α)û)/α) → totalSurplus μ α c = ∫ max(v − c, 0) d(postMeanLaw μ α), postMeanLaw the image of the prior under u ↦ αu + (1 − α)·priorMean μ; reason: the same quantity: G(·, α) is the CDF of that image law and (v − c)⁺ vanishes below c
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), proof of Corollary 1, unnumbered display, p. 30

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_measure
import Definitions.Def_InfoBargaining_SellerPayoff_totalSurplus

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **Exponential prior: closed form of `A(α, c)`.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022), proof of Corollary 1, unnumbered display, p. 30: "For the exponential prior
F(u) = 1 − e^{−u/û} for u ≥ 0, the total ex ante surplus is A(α, c) = û − c, for
α ≤ 1 − c/û; αû e^{((1−α)û−c)/(αû)}, for α ≥ 1 − c/û."

For every mean `û > 0`, every `α ∈ (0, 1)` and every real `c`.

**Formalization Note.** The printed "û − c, ," has a stray comma. Stated for every real `c`
(generalization of the paper's `c > 0`). -/
theorem exponential_totalSurplus_closed_form (uhat : ℝ) (h : 0 < uhat) :
    ∀ α ∈ Set.Ioo (0:ℝ) 1, ∀ c : ℝ,
      (α ≤ 1 - c / uhat →
        totalSurplus (FocalPrior.exponential uhat h).measure α c = uhat - c) ∧
      (1 - c / uhat ≤ α →
        totalSurplus (FocalPrior.exponential uhat h).measure α c =
          α * uhat * Real.exp (((1 - α) * uhat - c) / (α * uhat))) := by sorry

end InfoBargaining.SellerPayoff
