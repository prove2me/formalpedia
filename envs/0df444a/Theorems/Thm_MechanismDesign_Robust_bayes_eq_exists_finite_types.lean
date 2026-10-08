-- Prove2me | Theorems.Thm_MechanismDesign_Robust_bayes_eq_exists_finite_types
-- name    : MechanismDesign.Robust.bayes_eq_exists_finite_types
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:06:23.124462+00:00
-- url     : https://prove2.me/theorems/decf6a63-fe84-479f-a8a8-4547295537ab
-- title:
--   Proposition 10.5 -- finite mechanisms have Bayesian equilibria on the space of finite types
-- statement:
--   Let $(S_1,\dots,S_N,g)$ be a finite mechanism: every strategy set $S_i$ is finite. Then the mechanism has at least one Bayesian equilibrium in mixed strategies on the space $\mathcal T^+$ of all finite types, i.e. there are $\sigma_i : T^+_i \to \Delta(S_i)$ such that every finite type maximizes its expected utility, under its belief on $T^+_{-i}$, by playing $\sigma_i$.
--
--   Existence of equilibria is the reason for working on $\mathcal T^+$ rather than on the universal type space.
--
--   **Formalization Note** The outcome set is arbitrary; the hypothesis that each lottery $g(s)$ has a finite expected utility for every agent and payoff type profile is added so that expected utilities exist (the book leaves this implicit).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.181, Proposition 10.5, Definition 10.6

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.5 (Börgers p.181). Every finite mechanism (finite strategy sets `S_i`) has at
least one Bayesian equilibrium in mixed strategies on the space `T⁺` of finite types. The
hypothesis `hu` says that the expected utility of every lottery `g(s)` exists. -/
theorem bayes_eq_exists_finite_types {ι : Type} [Fintype ι] [DecidableEq ι] {Θ : ι → Type}
    [∀ i, Nonempty (Θ i)] {S : ι → Type} [∀ i, Fintype (S i)] {X : Type}
    (M : Mechanism S X) (u : ι → X → (∀ i, Θ i) → ℝ)
    (hu : ∀ s θ i, Summable fun x => (M.g s x).toReal * u i x θ) :
    ∃ σ : ∀ i, TPlusType Θ i → PMF (S i), IsBayesEq (TPlus Θ) u M σ := by sorry

end MechanismDesign.Robust
