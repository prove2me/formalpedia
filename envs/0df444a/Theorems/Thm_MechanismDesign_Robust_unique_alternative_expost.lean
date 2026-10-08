-- Prove2me | Theorems.Thm_MechanismDesign_Robust_unique_alternative_expost
-- name    : MechanismDesign.Robust.unique_alternative_expost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:06:40.66101+00:00
-- url     : https://prove2.me/theorems/66629795-16e2-4bef-aca2-257728251b4b
-- title:
--   Proposition 10.9 -- unique alternatives per payoff type profile are ex post implementable (corrected hypothesis)
-- statement:
--   Consider quasi-linear utilities $v_i(a,\theta) - t_i$ on outcomes $(a,t_1,\dots,t_N)$, on a type space in which every belief $\hat\beta_i(\tau_i)$ has finite support. Suppose the type space has **common certainties**: for every agent $i$ and payoff type profile $\theta_{-i}$ there is a belief, certain that the others' payoff types are $\theta_{-i}$, that is held by a type of every payoff type $\theta_i$ of agent $i$. Suppose a mechanism and a Bayesian equilibrium of it are such that for every $\theta \in \Theta$ the projection
--
--   $$\hat F(\theta) = \{a \in A : (a,t_1,\dots,t_N) \in F(\theta) \text{ for some } (t_1,\dots,t_N)\in\mathbb R^N\}$$
--
--   of the set $F(\theta)$ of equilibrium outcomes contains exactly one element. Then there is a reduced direct mechanism $(\tilde q,\tilde t)$ in which agents report their payoff types, the alternative implemented at the report $\theta$ is the unique element of $\hat F(\theta)$, and truth telling is an ex post Bayesian equilibrium.
--
--   The transfers are not pinned down; only the alternative is.
--
--   **Formalization Note** The book states the result under a large variety of certainties (Definition 10.7). With that hypothesis alone it is false: on a finite type space in which the low-value type of agent 1 is certain of one belief type of agent 2 and the high-value type is certain of another, the equilibrium can implement a decreasing allocation, which no ex post incentive-compatible reduced mechanism implements. The book's proof uses a type with payoff type $\theta_i'$ "with the same beliefs" as the deviating type; common certainties is exactly that requirement, and it holds on the universal type space and on the space of finite types. Beliefs are also required to have finite support, as they do on the space of finite types: with countably supported beliefs and unbounded interdependent valuations, a type whose belief spreads over infinitely many payoff profiles can have a finite expected utility in the original equilibrium but no reduced mechanism in which its expected utility exists, because the reduced mechanism cannot distinguish belief types that share a payoff type.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.188–189, Proposition 10.9 (hypothesis strengthened, see Formalization Note)

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.9 (Börgers p.189), quasi-linear version of Proposition 10.8, under the
common-certainty strengthening of Definition 10.7 that the book's proof uses (see the mission's
notes: with Definition 10.7 alone the statement is false), on a type space in which every belief
`β̂_i(τ_i)` has finite support (as on the space of finite types; with countably supported beliefs
and unbounded utilities the reduced mechanism's expected utilities need not exist, see the
mission's notes). Utilities are `v_i(a, θ) − t_i` on
outcomes `(a, t_1, …, t_N)`. Suppose `σ` is a Bayesian equilibrium of a mechanism such that for
every payoff type profile `θ` the projection `F̂(θ) = {a : (a, t) ∈ F(θ) for some t}` of the set
of equilibrium outcomes contains exactly one element. Then there is a reduced direct mechanism
`(q̃, t̃)` in which agents report their payoff types, the alternative implemented at the report `θ`
is the unique element of `F̂(θ)`, and truth telling is an ex post Bayesian equilibrium. -/
theorem unique_alternative_expost {ι : Type} [Fintype ι] [DecidableEq ι] {Θ T S : ι → Type*}
    {A : Type*} (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (hcc : ts.HasCommonCertainties) (hfin : ∀ i (τi : T i), (ts.β i τi).support.Finite)
    (M : Mechanism S (A × (ι → ℝ))) (σ : ∀ i, T i → PMF (S i))
    (hσ : IsBayesEq ts (qlUtility vu) M σ)
    (hF : ∀ θ, ∃ a, Prod.fst '' outcomeSet ts M σ θ = {a}) :
    ∃ (q : (∀ i, Θ i) → A) (t : ι → (∀ i, Θ i) → ℝ),
      (∀ θ, Prod.fst '' outcomeSet ts M σ θ = {q θ}) ∧
      IsExPostBayesEq ts (qlUtility vu) (qlReduced ts q t) (truthfulReduced ts) := by sorry

end MechanismDesign.Robust
