-- Prove2me | Theorems.Thm_MechanismDesign_Robust_belief_revelation
-- name    : MechanismDesign.Robust.belief_revelation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T05:06:14.565684+00:00
-- url     : https://prove2.me/theorems/dc29dd6b-8bf2-4e62-9717-a9e6325a1b03
-- title:
--   Proposition 10.6 -- on finite type spaces only payoff-type incentive constraints matter (Bergemann–Morris)
-- statement:
--   Consider quasi-linear utilities $v_i(a,\theta) - t_i$ with interdependent payoff types, and a finite type space $\mathcal T$ such that
--
--   1. for every agent $i$, no vector in the set of beliefs $\{\hat\beta_i(\tau_i) : \tau_i \in T_i\} \subseteq \mathbb R^{T_{-i}}$ can be written as a convex combination of the other vectors in this set;
--
--   and a direct mechanism $(q, t)$, $q : T \to A$, $t_i : T \to \mathbb R$, such that
--
--   2. for every agent $i$ and all $\tau_i, \tau_i' \in T_i$ with $\hat\beta_i(\tau_i) = \hat\beta_i(\tau_i')$, type $\tau_i$ has no incentive to pretend to be type $\tau_i'$ (when the others report truthfully).
--
--   Then there is another direct mechanism $(\tilde q,\tilde t)$ in which truth telling is a Bayesian equilibrium, such that
--
--   3. $\tilde q(\tau) = q(\tau)$ for every type profile $\tau \in T$;
--   4. for all agents $i$ and all types $\tau_i$, the interim expected payments coincide:
--
--   $$\sum_{\tau_{-i}} \hat\beta_i(\tau_i)(\tau_{-i})\,\tilde t_i(\tau_i,\tau_{-i}) = \sum_{\tau_{-i}} \hat\beta_i(\tau_i)(\tau_{-i})\, t_i(\tau_i,\tau_{-i}).$$
--
--   Incentive compatibility across belief types comes for free: when checking incentive compatibility one only has to check it between types with the same beliefs, and interim expected utilities are unchanged. The result generalizes the Crémer–McLean theorem (Proposition 6.4), whose condition fails as soon as two types share a belief.
--
--   **Formalization Note** Beliefs are vectors $\tau_{-i} \mapsto \hat\beta_i(\tau_i)(\tau_{-i})$ in $\mathbb R^{T_{-i}}$; condition 1 says each belief lies outside the convex hull of the other beliefs in the set (a belief held by several types appears once). "Truth telling is a Bayesian equilibrium" allows mixed misreports; condition 2 compares truthful reporting with a pure misreport. Alternatives and transfers are deterministic.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.183, Proposition 10.6 (Bergemann and Morris 2001, Proposition 4.5)

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.6 (Börgers p.183; Bergemann–Morris 2001, Prop. 4.5), belief revelation on a
finite type space with quasi-linear utilities `v_i(a, θ) − t_i`. Suppose
(i) for every agent `i`, no belief in the set `{β̂_i(τ_i) : τ_i ∈ T_i}` (as a vector in
`ℝ^{T_{-i}}`) is a convex combination of the other beliefs in that set, and the direct mechanism
`(q, t)` satisfies
(ii) for every agent `i` and types `τ_i, τ'_i` with `β̂_i(τ_i) = β̂_i(τ'_i)`, type `τ_i` has no
incentive to pretend to be `τ'_i` (others reporting truthfully).
Then there is another direct mechanism `(q̃, t̃)` in which truth telling is a Bayesian equilibrium,
such that (iii) `q̃(τ) = q(τ)` for every type profile `τ`, and (iv) every type `τ_i` has the same
interim expected payment in both mechanisms. -/
theorem belief_revelation {ι : Type} [Fintype ι] [DecidableEq ι] {Θ T : ι → Type*} {A : Type*}
    [∀ i, Fintype (T i)] (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (hconv : ∀ i (τi : T i), (fun τo => (ts.β i τi τo).toReal) ∉
      convexHull ℝ ((fun τi' : T i => fun τo => (ts.β i τi' τo).toReal) ''
        {τi' | ts.β i τi' ≠ ts.β i τi}))
    (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ)
    (hsame : ∀ i (τi τi' : T i), ts.β i τi = ts.β i τi' →
      interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi (PMF.pure τi') ≤
        interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi (PMF.pure τi)) :
    ∃ (q' : (∀ i, T i) → A) (t' : ι → (∀ i, T i) → ℝ),
      IsBayesEq ts (qlUtility vu) (qlDirect ts q' t') (truthful T) ∧
      (∀ τ, q' τ = q τ) ∧
      ∀ i (τi : T i), interimPayment ts t' i τi = interimPayment ts t i τi := by sorry

end MechanismDesign.Robust
