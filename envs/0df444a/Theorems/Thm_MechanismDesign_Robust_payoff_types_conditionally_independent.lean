-- Prove2me | Theorems.Thm_MechanismDesign_Robust_payoff_types_conditionally_independent
-- name    : MechanismDesign.Robust.payoff_types_conditionally_independent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T04:49:27.765999+00:00
-- url     : https://prove2.me/theorems/769be6aa-e7a0-403d-8489-8461f67c9012
-- title:
--   Proposition 10.1 -- with a full-support common prior, payoff types are independent given belief types
-- statement:
--   Let $\mathcal T = (T_i,\hat\theta_i,\hat\beta_i)_{i\in I}$ be a finite type space whose beliefs are derived from a common prior $\mu$ on $T_1\times\dots\times T_N$ with full support ($\mu(\tau) > 0$ for every type profile $\tau$). Then for every profile of belief types $\beta \in \prod_{i\in I}\hat\beta_i(T_i)$ and every payoff type profile $(\theta_1,\dots,\theta_N)$,
--
--   $$\mu\big((\theta_1,\dots,\theta_N)\mid\beta\big) = \mu(\theta_1\mid\beta)\,\mu(\theta_2\mid\beta)\cdots\mu(\theta_N\mid\beta),$$
--
--   where $\mu(\theta\mid\beta)$ is the probability under $\mu$ that the payoff type profile is $\theta$ conditional on the belief type profile being $\beta$, and $\mu(\theta_i\mid\beta)$ the conditional probability that agent $i$'s payoff type is $\theta_i$.
--
--   Conditional on all belief types, payoff types are independent. This is what allows optimal mechanisms on common-prior type spaces to be built in two steps: elicit belief types, then solve an independent-types problem.
--
--   **Formalization Note** Conditional probabilities are ratios in $[0,\infty]$; the conditioning event $\{\hat\beta(\tau) = \beta\}$ has positive probability because $\beta$ is realized by some type profile and $\mu$ has full support.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.174, Proposition 10.1

import Mathlib
import Definitions.Def_MechanismDesign_Robust_TypeSpaces

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.1 (Börgers p.174). In a finite type space whose beliefs are derived from a
common prior `μ` with full support, conditional on any profile of belief types
`β ∈ ∏_i β̂_i(T_i)`, the payoff types are independent:
`μ((θ_1, …, θ_N) | β) = μ(θ_1 | β) ⋯ μ(θ_N | β)` for every payoff type profile `θ`. -/
theorem payoff_types_conditionally_independent {ι : Type} [Fintype ι] [DecidableEq ι]
    {Θ : ι → Type*} {T : ι → Type*} [∀ i, Fintype (T i)] (ts : TypeSpace Θ T)
    (μ : PMF (∀ i, T i)) (hμ : ts.IsCommonPrior μ) (hfull : ∀ τ, μ τ ≠ 0)
    (β : ∀ i, PMF (Others T i)) (hβ : ∀ i, β i ∈ Set.range (ts.β i)) (θ : ∀ i, Θ i) :
    condProb μ {τ | ts.payoff τ = θ} {τ | ts.beliefs τ = β} =
      ∏ i, condProb μ {τ | ts.payoff τ i = θ i} {τ | ts.beliefs τ = β} := by sorry

end MechanismDesign.Robust
