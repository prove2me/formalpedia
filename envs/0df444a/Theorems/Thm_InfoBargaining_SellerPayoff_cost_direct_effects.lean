-- Prove2me | Theorems.Thm_InfoBargaining_SellerPayoff_cost_direct_effects
-- name    : InfoBargaining.SellerPayoff.cost_direct_effects
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:23:30.232088+00:00
-- url     : https://prove2.me/theorems/67f17c39-0a16-438d-a9fb-d7770e3e15bd
-- title:
--   Direct effects of the cost: $A(\alpha,c)$ nonincreasing, $c+\theta_sA(\alpha,c)$ increasing in $c$
-- statement:
--   A seller and a buyer may trade one unit. Trade costs the seller $c>0$ and is worth $u$ to the buyer, who does not know $u$; the prior law of $u$ is $F$ with mean $\hat u>0$. Before negotiating, the buyer buys a truth-or-noise signal of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$; its posterior mean is $v=\alpha w+(1-\alpha)\hat u$, whose law is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$. The parties then split the net surplus $v-c$ in proportion to their bargaining powers $\theta_s,\theta_b\in(0,1)$, $\theta_s+\theta_b=1$.
--
--   Let $P$ be any of the four focal priors, $\alpha\in(0,1)$ and $\theta_s\in(0,1)$. Then
--
--   1. $c\mapsto A(\alpha,c)$ is nonincreasing on $\mathbb R$;
--   2. at every admissible cost $c$, the map $x\mapsto x+\theta_sA(\alpha,x)$ is differentiable and
--
--   $$
--   \frac{\partial}{\partial c}\big[c+\theta_sA(\alpha,c)\big]=1+\theta_s\frac{\partial A(\alpha,c)}{\partial c}>0.
--   $$
--
--   These are the direct effects of the cost, holding the buyer's information fixed: a higher material cost lowers the total surplus, and a higher opportunity cost raises the seller's payoff $V_s^*$.
--
--   Differences from the source:
--   - generalization: at α = α∗ → at every fixed α ∈ (0, 1); reason: a direct effect holds α fixed; α∗ ∈ [α̲, ᾱ] ⊆ (0, 1) is an instance
--   - generalization: A(α∗, c) lower as c increases, c in the model's domain → Antitone on all of ℝ (weak); reason: holds for every real c; weak because A(α, ·) = 0 beyond the support for the uniform and modified pareto priors
--   - encoding: 1 + θ_s ∂A(α∗, c)/∂c becomes positive → 0 < deriv (fun x => x + θ_s A(α, x)) c; reason: in Lean deriv is 0 at a non-differentiable point, so the statement also asserts differentiability, which holds since the focal priors are atomless
--   - encoding: A(α, c) = ∫_c^v̄ (v − c) dG(v, α) with G(v, α) = F((v − (1 − α)û)/α) → totalSurplus μ α c = ∫ max(v − c, 0) d(postMeanLaw μ α), postMeanLaw the image of the prior under u ↦ αu + (1 − α)·priorMean μ; reason: the same quantity: G(·, α) is the CDF of that image law and (v − c)⁺ vanishes below c
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §3.2, unnumbered, p. 12 ("The direct effect of increasing c clearly results in a lower total ex ante surplus") and p. 13 ("The direct effect of increasing c, 1 + θs∂A(α∗, c)/∂c, becomes positive")

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_measure
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_costDomain
import Definitions.Def_InfoBargaining_SellerPayoff_totalSurplus

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **Direct effects of the cost: `A(α, c)` is nonincreasing in `c`; `c + θ_s A(α, c)` has positive derivative.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022), §3.2, unnumbered, p. 12: "The direct effect of increasing c clearly results in a lower
total ex ante surplus A(α∗, c)."; p. 13: "The direct effect of increasing c,
1 + θ_s ∂A(α∗, c)/∂c, becomes positive (as in the benchmark)."

For every focal prior, every `α ∈ (0, 1)` and `θ_s ∈ (0, 1)`: `c ↦ A(α, c)` is antitone on
`ℝ`, and at every admissible cost `c` the map `x ↦ x + θ_s A(α, x)` is differentiable with
positive derivative.

**Formalization Note.** Antitone on all of `ℝ` (generalization of "on the domain"); weak,
since `A(α, ·) = 0` beyond the support for the uniform and modified pareto priors. "Positive" is
`0 < deriv`, which in Lean also asserts differentiability (`deriv` is `0` at a
non-differentiable point). -/
theorem cost_direct_effects (P : FocalPrior) :
    ∀ α ∈ Set.Ioo (0:ℝ) 1, ∀ θs ∈ Set.Ioo (0:ℝ) 1,
      Antitone (fun c => totalSurplus P.measure α c) ∧
      ∀ c ∈ P.costDomain, 0 < deriv (fun x => x + θs * totalSurplus P.measure α x) c := by sorry

end InfoBargaining.SellerPayoff
