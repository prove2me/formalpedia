-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_theorem_1
-- name    : MaintPOMDP.Frontier.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:18.031039+00:00
-- url     : https://prove2.me/theorems/9d219e96-6ea9-4edd-8b88-49cdaf7b8e28
-- title:
--   Theorem 1, p. 21 — under {P, R} the optimal solution is [P], R[P] or [PR]
-- statement:
--   Under the standing assumptions, consider the two-action model $\{P,R\}$ and write
--   $$\theta=\frac{c^P+\beta\gamma_1c^F}{1-\beta+\beta(\gamma_0+\gamma_1)} .$$
--   The optimal solution $(U^\dagger,u^\dagger_F)$ has one of three structures:
--   1. **No replacement $[P]$.** If $c^R\ge\theta$, then $U^\dagger=\{\mathbf u^{(\dot P)}\}$ and $u^\dagger_F=u_F^{(\dot P)}$.
--   2. **Transient replacement $R[P]$.** If $\frac{\gamma_0}{\gamma_1}\theta\le c^R<\theta$, then $U^\dagger=\{\mathbf u^{(\dot P)},\mathbf u^{(R\dot P)}\}$ with $\mathbf u^{(R\dot P)}=(c^R+u_0^{(\dot P)},c^R+u_0^{(\dot P)})'$, both points are extreme, and $u^\dagger_F=u_F^{(\dot P)}$.
--   3. **Recurrent replacement $[PR]$.** If $c^R<\min\{\frac{\gamma_0}{\gamma_1}\theta,\theta\}$, then there is a least minimizer $m^\dagger$ of $f$ over $\{0,1,\dots\}$, and with $u^R=f(m^\dagger)$, $\mathbf u_0=(u^R,u^R)'$, $u^\dagger_F=u^R+c^F-c^R$ and $\mathbf u_{i+1}=\mathbf g^P(u^\dagger_F)+\beta\mathbf P^P\mathbf u_i$,
--   $$U^\dagger=\{\mathbf u_i:i=0,1,\dots,n^\dagger\},\qquad n^\dagger=m^\dagger+1,$$
--   and every listed point is an extreme point of $U^\dagger$.
--
--   Here "$(U,u_F)$ is the optimal solution" means that value iteration for $\{P,R\}$ from zero terminal costs converges to $\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ for every belief $\boldsymbol\pi\ge0$ and to $u_F$ after a failure. The theorem is the building block of Theorem 2.
--
--   **Formalization Note** The ranges $0<\gamma_0,\gamma_1<1$ are added (the threshold divides by $\gamma_1$). "$m^\dagger=\arg\min f$" is read as the least minimizer, as in the proof (EC p. 8); its existence is part of the conclusion. $f$ is defined through the anchor equation of Lemma 3. Extreme points are in the sense of §3.3: each point is the strict minimizer of $\boldsymbol\pi'\cdot$ over the set for some $\boldsymbol\pi$ in the closed simplex.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), p. 21, Theorem 1; proof EC pp. 4–8

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Theorem 1 (p. 21): under actions {P, R} the optimal solution (U†, u†_F) is
(1) [P] ({u^(Ṗ)}, u_F^(Ṗ)) if c^R ≥ thrP;
(2) R[P] ({u^(Ṗ), u^(RṖ)}, u_F^(Ṗ)), both points extreme, if (γ0/γ1)·thrP ≤ c^R < thrP;
(3) [PR] if c^R < min{(γ0/γ1)·thrP, thrP}: with m† the least minimizer of f over ℕ,
U† = {u_0, …, u_{m†+1}} (all extreme) from u_0 = (f(m†), f(m†))′, and u†_F = f(m†) + c^F − c^R.
Here thrP = (c^P + βγ1c^F)/(1 − β + β(γ0 + γ1)). -/
theorem theorem_1 (M : Params) (hM : M.Standing) :
    (M.thrP ≤ M.cR → M.Solves ActSet.PR {M.uPdot} M.uFPdot) ∧
    (M.γ0 / M.γ1 * M.thrP ≤ M.cR → M.cR < M.thrP →
      M.Solves ActSet.PR {M.uPdot, M.uRPdot} M.uFPdot ∧ IsExtremeSet {M.uPdot, M.uRPdot}) ∧
    (M.cR < min (M.γ0 / M.γ1 * M.thrP) M.thrP →
      ∃ mdag : ℕ, IsLeastMin M.f mdag ∧
        M.Solves ActSet.PR (M.Udag mdag) (M.f mdag + M.cF - M.cR) ∧
        IsExtremeSet (M.Udag mdag)) := by sorry

end MaintPOMDP.Frontier
