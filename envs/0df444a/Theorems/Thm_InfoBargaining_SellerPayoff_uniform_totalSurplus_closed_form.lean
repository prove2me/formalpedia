-- Prove2me | Theorems.Thm_InfoBargaining_SellerPayoff_uniform_totalSurplus_closed_form
-- name    : InfoBargaining.SellerPayoff.uniform_totalSurplus_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:17:58.152979+00:00
-- url     : https://prove2.me/theorems/10863483-6851-4ca1-bd66-4af8919911ab
-- title:
--   Uniform prior: closed form of $A(\alpha,c)$
-- statement:
--   A seller and a buyer may trade one unit. Trade costs the seller $c>0$ and is worth $u$ to the buyer, who does not know $u$; the prior law of $u$ is $F$ with mean $\hat u>0$. Before negotiating, the buyer buys a truth-or-noise signal of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$; its posterior mean is $v=\alpha w+(1-\alpha)\hat u$, whose law is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$. The parties then split the net surplus $v-c$ in proportion to their bargaining powers $\theta_s,\theta_b\in(0,1)$, $\theta_s+\theta_b=1$.
--
--   For the uniform prior $F(u)=u$ on $[0,1]$ (so $\hat u=1/2$), for every $\alpha\in(0,1)$ and every real $c$,
--
--   $$
--   A(\alpha,c)=\begin{cases}\max\{1/2-c,\,0\}, & \alpha\le|1-2c|,\\[4pt] \dfrac{[(1+\alpha)/2-c]^2}{2\alpha}, & \alpha\ge|1-2c|.\end{cases}
--   $$
--
--   The two branches agree at $\alpha=|1-2c|$. This is the paper's running example, used to compute the thresholds of Corollary 1 explicitly.
--
--   Differences from the source:
--   - generalization: c in the model's domain c ∈ (0, 1) → every real c; reason: the closed form holds for every real c (outside the support only the first branch applies); it specializes to the paper's range
--   - encoding: A(α, c) = ∫_c^v̄ (v − c) dG(v, α) with G(v, α) = F((v − (1 − α)û)/α) → totalSurplus μ α c = ∫ max(v − c, 0) d(postMeanLaw μ α), postMeanLaw the image of the prior under u ↦ αu + (1 − α)·priorMean μ; reason: the same quantity: G(·, α) is the CDF of that image law and (v − c)⁺ vanishes below c
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §3.2, unnumbered display, p. 13

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_measure
import Definitions.Def_InfoBargaining_SellerPayoff_totalSurplus

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **Uniform prior: closed form of the total ex ante surplus `A(α, c)`.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022), §3.2, unnumbered display, p. 13: "Take the uniform distribution as an example: F(u) = u
with support [0, 1] and mean û = 1/2 … The total ex ante surplus in (7) can be reduced as
A(α, c) = max{1/2 − c, 0}, for α ≤ |1 − 2c|; [(1 + α)/2 − c]²/(2α), for α ≥ |1 − 2c|."

For every `α ∈ (0, 1)` and every real `c`, both branches as printed (closed ranges; they agree
at `α = |1 − 2c|`).

**Formalization Note.** Stated for every real `c`, not only the paper's `c ∈ (0, 1)`; for `c`
outside `[0, 1]` only the first branch applies and it is still correct (generalization). -/
theorem uniform_totalSurplus_closed_form :
    ∀ α ∈ Set.Ioo (0:ℝ) 1, ∀ c : ℝ,
      (α ≤ |1 - 2 * c| → totalSurplus FocalPrior.uniform.measure α c = max (1 / 2 - c) 0) ∧
      (|1 - 2 * c| ≤ α →
        totalSurplus FocalPrior.uniform.measure α c = ((1 + α) / 2 - c) ^ 2 / (2 * α)) := by sorry

end InfoBargaining.SellerPayoff
