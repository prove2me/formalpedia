-- Prove2me | Theorems.Thm_MechanismDesign_Correlated_revenue_equivalence
-- name    : MechanismDesign.Correlated.revenue_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T02:44:36.604049+00:00
-- url     : https://prove2.me/theorems/295ec00c-d80c-4ed1-83d2-64e029eaeffb
-- title:
--   Proposition 6.2 — Bayesian revenue equivalence for convex type sets and convex utilities (independent types)
-- statement:
--   **Proposition 6.2.** Let types be independent (the prior is a product $\rho_1\otimes\dots\otimes\rho_N$). Suppose that every type set $\Theta_i$ is a convex subset of a finite-dimensional Euclidean space $\mathbb R^{d_i}$ and that for every agent $i$ and alternative $a$ the utility $u_i(a,\theta_i)$ is a convex function of $\theta_i \in \Theta_i$ (continuous on $\Theta_i$; see the note). Let $(q, t_1,\dots,t_N)$ and $(q', t'_1,\dots,t'_N)$ be Bayesian incentive-compatible direct mechanisms with interim decision rules $Q_i$, $Q_i'$ and interim expected payments $T_i$, $T_i'$. If
--   $$Q_i'(\theta_i) = Q_i(\theta_i) \quad\text{for every } i\in I \text{ and } \theta_i\in\Theta_i,$$
--   then for every $i \in I$ there is a number $\tau_i \in \mathbb R$ such that
--   $$T_i'(\theta_i) = T_i(\theta_i) + \tau_i \quad\text{for every } \theta_i \in \Theta_i.$$
--
--   This is the Bayesian version of the revenue equivalence theorem of Krishna and Maenner (2001) (Proposition 5.8): the interim decision rules pin down the interim payment rules up to a constant for each agent.
--
--   **Formalization Note** The utility is given as $v_i(a,\cdot)$ on all of $\mathbb R^{d_i}$, but only its values on $\Theta_i$ enter. Continuity of $v_i(a,\cdot)$ on $\Theta_i$ is **added** to the book's hypotheses: a convex function on a convex set that is not open may jump up at the boundary, and then the statement fails (one agent, $\Theta = [0,1]$, $A=\{a_0,a_1\}$, $u(a_0,\theta)=0$, $u(a_1,\theta)=\mathbf 1\{\theta=1\}$, $q(\theta)=a_1$ iff $\theta=1$: every payment $T(1)-T(0)\in[0,1]$ is incentive compatible). Every convex function on an open set, and every convex function on $\mathbb R^{d_i}$ restricted to $\Theta_i$, satisfies it. Measurability conventions as in the definition file.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.117–118, Proposition 6.2

import Mathlib
import Definitions.Def_MechanismDesign_Correlated_IndepModel

namespace MechanismDesign.Correlated

open MeasureTheory Indep

/-- Börgers, Proposition 6.2 (pp.117–118), revenue equivalence after Krishna and Maenner (2001).
Types are independent; agent `i`'s type set is a convex subset `S i` of a Euclidean space
`ℝ^{d i}`, and each `uᵢ(a, ·)` is convex (and continuous, see the natural-language statement) on
`S i`. If two Bayesian incentive-compatible direct mechanisms have the same interim decision rules
`Qᵢ(θᵢ)`, then for every agent `i` their interim expected payments differ by a constant `τᵢ`. -/
theorem revenue_equivalence {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    (S : ∀ i, Set (EuclideanSpace ℝ (Fin (d i)))) (hS : ∀ i, Convex ℝ (S i))
    {A : Type*} [MeasurableSpace A] (v : ∀ i, A → EuclideanSpace ℝ (Fin (d i)) → ℝ)
    (hv_convex : ∀ i a, ConvexOn ℝ (S i) (v i a))
    (hv_cont : ∀ i a, ContinuousOn (v i a) (S i))
    (ρ : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (ρ i)]
    (M M' : DirectMechanism ι (fun i => S i) A)
    (hM : IsMechanism ρ (fun i a θ => v i a θ) M) (hM' : IsMechanism ρ (fun i a θ => v i a θ) M')
    (hBIC : IsBIC ρ (fun i a θ => v i a θ) M) (hBIC' : IsBIC ρ (fun i a θ => v i a θ) M')
    (hQ : ∀ i (θi : S i), interimDist ρ M'.q i θi = interimDist ρ M.q i θi) :
    ∀ i, ∃ τ : ℝ, ∀ θi : S i, interimTransfer ρ M'.t i θi = interimTransfer ρ M.t i θi + τ := by sorry

end MechanismDesign.Correlated
