-- Prove2me | Theorems.Thm_MechanismDesign_Robust_expost_revelation_principle
-- name    : MechanismDesign.Robust.expost_revelation_principle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:06:16.70258+00:00
-- url     : https://prove2.me/theorems/baeb2b2f-5088-4037-9884-843123406d68
-- title:
--   Proposition 10.4 -- belief-independent equilibria are ex post under a large variety of certainties
-- statement:
--   Let $\sigma^*$ be a belief-independent Bayesian equilibrium of a mechanism $(S_1,\dots,S_N,g)$ on a type space with a large variety of certainties. Then:
--
--   1. $\sigma^*$ is an ex post Bayesian equilibrium of the mechanism;
--   2. in the reduced direct mechanism $\tilde S_i = \Theta_i$, $\tilde g(\theta) = g(\sigma^*_1(\tau_1),\dots,\sigma^*_N(\tau_N))$ for any $\tau$ with $\hat\theta(\tau) = \theta$, truthful reporting of payoff types $\tilde\sigma^*_i(\tau_i) = \hat\theta_i(\tau_i)$ is an ex post Bayesian equilibrium,
--
--   and this equilibrium is outcome equivalent to $\sigma^*$ at every type profile.
--
--   Under a large variety of certainties, simple equilibria in simple mechanisms are necessarily robust to what agents learn about the others' types.
--
--   **Formalization Note** As in Proposition 10.3, the reduced mechanism is asserted to exist with $\tilde g(\hat\theta(\tau)) = g(\sigma^*(\tau))$ for all $\tau$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.180–181, Proposition 10.4, Definitions 10.7, 10.13

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.4 (Börgers pp.180–181). Let `σ` be a belief-independent Bayesian equilibrium
of `(S_1, …, S_N, g)` on a type space with a large variety of certainties. Then `σ` is an ex post
Bayesian equilibrium; moreover there is a reduced direct mechanism `g̃` with
`g̃(θ̂(τ)) = g(σ_1(τ_1), …, σ_N(τ_N))` for every `τ` in which truthful reporting of payoff types is an
ex post Bayesian equilibrium, outcome equivalent to `σ`. -/
theorem expost_revelation_principle {ι : Type} [Fintype ι] [DecidableEq ι]
    {Θ T S : ι → Type*} {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (hlv : ts.HasLargeVarietyOfCertainties)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (hσ : IsBayesEq ts u M σ)
    (hbi : IsBeliefIndependent ts σ) :
    IsExPostBayesEq ts u M σ ∧
      ∃ g' : (∀ i, Θ i) → PMF X, (∀ τ x, g' (ts.payoff τ) x = eqOutcome M σ τ x) ∧
        IsExPostBayesEq ts u (reducedMechanism ts g') (truthfulReduced ts) ∧
        ∀ τ x, eqOutcome (reducedMechanism ts g') (truthfulReduced ts) τ x =
          eqOutcome M σ τ x := by sorry

end MechanismDesign.Robust
