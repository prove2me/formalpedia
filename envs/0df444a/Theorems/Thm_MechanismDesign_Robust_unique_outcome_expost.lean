-- Prove2me | Theorems.Thm_MechanismDesign_Robust_unique_outcome_expost
-- name    : MechanismDesign.Robust.unique_outcome_expost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:06:46.009854+00:00
-- url     : https://prove2.me/theorems/7163fe3e-dc67-4ba7-9365-b018050cef51
-- title:
--   Proposition 10.8 -- unique outcomes per payoff type profile are ex post implementable
-- statement:
--   Suppose the type space has a large variety of certainties, and that a mechanism and a Bayesian equilibrium $\sigma$ of it are such that for every payoff type profile $\theta \in \Theta$ the set $F(\theta)$ — the outcomes that occur with positive probability at some type profile with payoff types $\theta$ — contains exactly one element $f(\theta)$. Then in the reduced direct mechanism in which agents report their payoff types and the unique outcome $f(\theta)$ in $F(\theta)$ is implemented, truth telling is an ex post Bayesian equilibrium.
--
--   If the designer implements a unique outcome for every payoff type profile, she may restrict attention to reduced direct mechanisms and ex post equilibria.
--
--   **Formalization Note** Utilities are general (non-transferable, interdependent). $F(\theta)$ is the union over type profiles $\tau$ with $\hat\theta(\tau) = \theta$ of the supports of the equilibrium outcome lotteries.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.188, Proposition 10.8

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.8 (Börgers p.188). Suppose the type space has a large variety of
certainties and `σ` is a Bayesian equilibrium of a mechanism such that for every payoff type
profile `θ` the set `F(θ)` of equilibrium outcomes at type profiles with payoff types `θ`
contains exactly one element `f(θ)`. Then in the reduced direct mechanism in which agents report
their payoff types and `f(θ)` is implemented, truth telling is an ex post Bayesian equilibrium. -/
theorem unique_outcome_expost {ι : Type} [Fintype ι] [DecidableEq ι] {Θ T S : ι → Type*}
    {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (hlv : ts.HasLargeVarietyOfCertainties)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (hσ : IsBayesEq ts u M σ)
    (f : (∀ i, Θ i) → X) (hF : ∀ θ, outcomeSet ts M σ θ = {f θ}) :
    IsExPostBayesEq ts u (reducedMechanism ts (fun θ => PMF.pure (f θ))) (truthfulReduced ts) := by sorry

end MechanismDesign.Robust
