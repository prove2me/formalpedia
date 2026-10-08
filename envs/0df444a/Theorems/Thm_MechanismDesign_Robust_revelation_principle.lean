-- Prove2me | Theorems.Thm_MechanismDesign_Robust_revelation_principle
-- name    : MechanismDesign.Robust.revelation_principle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T05:05:49.050014+00:00
-- url     : https://prove2.me/theorems/d0dfe083-eba1-4e8a-903d-54b49475656c
-- title:
--   Proposition 10.2 -- the revelation principle on a type space
-- statement:
--   Let $\sigma^* = (\sigma^*_1,\dots,\sigma^*_N)$ be a Bayesian equilibrium of a mechanism $(S_1,\dots,S_N,g)$ on a type space $\mathcal T$. Construct the direct mechanism $(\tilde S_1,\dots,\tilde S_N,\tilde g)$ with $\tilde S_i = T_i$ and
--
--   $$\tilde g(\tau_1,\dots,\tau_N) = g\big(\sigma^*_1(\tau_1),\dots,\sigma^*_N(\tau_N)\big) \quad\text{for all } \tau \in T,$$
--
--   the lottery over outcomes induced by the equilibrium at $\tau$. Then truth telling, $\tilde\sigma^*_i(\tau_i) = \tau_i$, is a Bayesian equilibrium of the direct mechanism, and it is outcome equivalent to $\sigma^*$: at every type profile the outcome lottery is the same in both mechanisms and their equilibria.
--
--   The revelation principle lets the modeller restrict attention to direct mechanisms and truthful equilibria on any given type space.
--
--   **Formalization Note** The statement asserts that the lottery-valued function $\tilde g$ exists (the induced weights sum to one), that truth telling is a Bayesian equilibrium of the direct mechanism it defines, and outcome equivalence.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.179, Proposition 10.2

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.2 (Börgers p.179), the revelation principle on a type space. If `σ` is a
Bayesian equilibrium of the mechanism `(S_1, …, S_N, g)`, then the direct mechanism
`g̃(τ) = g(σ_1(τ_1), …, σ_N(τ_N))` (the lottery induced by `σ` at `τ`) exists, truth telling is a
Bayesian equilibrium of it, and it is outcome equivalent: at every type profile the truthful
outcome lottery of `g̃` equals the equilibrium outcome lottery of `g`. -/
theorem revelation_principle {ι : Type} [Fintype ι] [DecidableEq ι] {Θ T S : ι → Type*}
    {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ) (M : Mechanism S X)
    (σ : ∀ i, T i → PMF (S i)) (hσ : IsBayesEq ts u M σ) :
    ∃ g' : (∀ i, T i) → PMF X, (∀ τ x, g' τ x = eqOutcome M σ τ x) ∧
      IsBayesEq ts u (directMechanism ts g') (truthful T) ∧
      ∀ τ x, eqOutcome (directMechanism ts g') (truthful T) τ x = eqOutcome M σ τ x := by sorry

end MechanismDesign.Robust
