-- Prove2me | Theorems.Thm_MechanismDesign_Robust_reduced_revelation_principle
-- name    : MechanismDesign.Robust.reduced_revelation_principle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T05:05:48.547988+00:00
-- url     : https://prove2.me/theorems/78416784-5517-4149-8da1-a52a00ee5923
-- title:
--   Proposition 10.3 -- the revelation principle for belief-independent equilibria
-- statement:
--   Let $\sigma^*$ be a belief-independent Bayesian equilibrium of a mechanism $(S_1,\dots,S_N,g)$ on a type space $\mathcal T$. Construct a reduced direct mechanism $(\tilde S_1,\dots,\tilde S_N,\tilde g)$ with $\tilde S_i = \Theta_i$ and
--
--   $$\tilde g(\theta_1,\dots,\theta_N) = g\big(\sigma^*_1(\tau_1),\dots,\sigma^*_N(\tau_N)\big),$$
--
--   where $\tau_i$ is some type of agent $i$ with $\hat\theta_i(\tau_i) = \theta_i$ (by belief independence the choice does not matter). Then reporting one's payoff type, $\tilde\sigma^*_i(\tau_i) = \hat\theta_i(\tau_i)$, is a Bayesian equilibrium of the reduced direct mechanism, and it is outcome equivalent to $\sigma^*$ at every type profile.
--
--   Belief-independent equilibria can thus be implemented by mechanisms that only ask for payoff types.
--
--   **Formalization Note** Stated as: there is a lottery-valued $\tilde g$ on payoff type profiles with $\tilde g(\hat\theta(\tau)) = g(\sigma^*(\tau))$ for every type profile $\tau$ such that the conclusions hold. At payoff type profiles that no type profile realizes, the book's construction is undefined and $\tilde g$ may be chosen freely.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.180, Proposition 10.3, Definition 10.12

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.3 (Börgers p.180), the revelation principle for belief-independent
equilibria. If `σ` is a belief-independent Bayesian equilibrium of `(S_1, …, S_N, g)`, there is a
reduced direct mechanism `g̃ : Θ → Δ(X)` with `g̃(θ̂(τ)) = g(σ_1(τ_1), …, σ_N(τ_N))` for every type
profile `τ` (the book's `g̃(θ) = g(σ(τ))` for any `τ` with `θ̂(τ) = θ`), in which reporting one's
payoff type, `σ̃_i(τ_i) = θ̂_i(τ_i)`, is a Bayesian equilibrium that is outcome equivalent to `σ`. -/
theorem reduced_revelation_principle {ι : Type} [Fintype ι] [DecidableEq ι]
    {Θ T S : ι → Type*} {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (hσ : IsBayesEq ts u M σ)
    (hbi : IsBeliefIndependent ts σ) :
    ∃ g' : (∀ i, Θ i) → PMF X, (∀ τ x, g' (ts.payoff τ) x = eqOutcome M σ τ x) ∧
      IsBayesEq ts u (reducedMechanism ts g') (truthfulReduced ts) ∧
      ∀ τ x, eqOutcome (reducedMechanism ts g') (truthfulReduced ts) τ x = eqOutcome M σ τ x := by sorry

end MechanismDesign.Robust
