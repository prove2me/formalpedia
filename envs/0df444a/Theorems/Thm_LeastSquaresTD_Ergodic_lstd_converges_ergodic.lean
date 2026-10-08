-- Prove2me | Theorems.Thm_LeastSquaresTD_Ergodic_lstd_converges_ergodic
-- name    : LeastSquaresTD.Ergodic.lstd_converges_ergodic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:18:28.079115+00:00
-- url     : https://prove2.me/theorems/8d423316-74cb-4f93-9d1f-38f0ef893d01
-- title:
--   Theorem 2 — LS TD converges with probability 1 to θ* on ergodic Markov chains
-- statement:
--   Let $P$ be the transition matrix of an ergodic (irreducible) Markov chain on a finite nonempty state set $X$, with transition rewards $R(x,y)$, expected rewards $\bar r_x=\sum_yP(x,y)R(x,y)$ and discount factor $\gamma$, and let $V(x)=\sum_{k\ge0}\gamma^k(P^k\bar r)(x)$ be its value function. Run LS TD as in Figure 3: the states $Z_0,Z_1,\dots$ follow the chain from an arbitrary initial law, and after $t$ transitions
--   $$\theta_t=\Big[\frac1t\sum_{k=0}^{t-1}\phi_{Z_k}\big(\phi_{Z_k}-\gamma\phi_{Z_{k+1}}\big)'\Big]^{-1}\Big[\frac1t\sum_{k=0}^{t-1}\phi_{Z_k}R(Z_k,Z_{k+1})\Big].$$
--   Suppose
--
--   1. the feature vectors $\{\phi_x\mid x\in X\}$ are linearly independent;
--   2. each $\phi_x$ has dimension $N=|X|$;
--   3. $0<\gamma<1$.
--
--   Then $\theta^*$ is finite — the value series converges and there is $\theta^*\in\mathbb R^N$ with $V(x)=\phi_x'\theta^*$ for every $x$ — and
--   $$\theta_t\longrightarrow\theta^*\quad\text{with probability }1\text{ as }t\to\infty .$$
--
--   Together with Theorem 1 (absorbing chains), this is the paper's main convergence guarantee for LS TD, the analogue for linear least-squares TD of the probability-one convergence results of Tsitsiklis and of Watkins and Dayan for tabular TD(0).
--
--   **Formalization Note** The paper's "ergodic" is formalized as irreducible (periodic chains allowed). The path is a Markov chain with transition matrix $P$ on an arbitrary probability space; the theorem is quantified over every initial law, which contains Figure 3's arbitrary initial state. The estimate uses the transitions observed so far ($k=0,\dots,t-1$), an index shift of the printed (11) that does not affect the limit; where the matrix in (11) is singular Lean's inverse returns $0$, which does not affect convergence. "$\theta_{\rm LSTD}$ converges to $\theta^*$" (with $\theta_{\rm LSTD}=\lim_t\theta_t$) is formalized as $\theta_t\to\theta^*$. $\theta^*$ is not defined by a formula: it is any vector with $V=\Phi\theta^*$ (unique by linear independence).
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), p. 44, Theorem 2 (Convergence of LS TD for ergodic Markov chains); Figure 3, p. 43; Eq. (11), p. 42

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain
import Definitions.Def_LeastSquaresTD_Ergodic_LSTD
open MeasureTheory Matrix Filter Topology

namespace LeastSquaresTD.Ergodic

/-- Theorem 2 (Convergence of LS TD for ergodic Markov chains), p. 44. Run LS TD as in Figure 3
on an ergodic (irreducible) finite Markov chain from an arbitrary initial law. If (1) the feature
vectors `{φₓ | x ∈ X}` are linearly independent, (2) each `φₓ` has dimension `N = |X|`, and
(3) `0 < γ < 1`, then `θ*` is finite (the value series converges and `V(x) = φₓ'θ*`) and the
LS TD estimates `θₜ` of (11) converge to `θ*` with probability 1 as the number of state
transitions tends to infinity. -/
theorem lstd_converges_ergodic {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (hC : C.IsErgodic) (R : X → X → ℝ)
    {m : ℕ} (φ : X → Fin m → ℝ) (hφ : LinearIndependent ℝ φ) (hm : m = Fintype.card X)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : X → ℝ) (hν : IsProbVec ν) (Z : ℕ → Ω → X) (hZ : IsMarkovLaw μ C ν Z) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k * ((C.P ^ k) *ᵥ C.rbar R) x)) ∧
      (∀ x, C.value R γ x = φ x ⬝ᵥ θstar) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun t : ℕ => lstdTheta φ R γ t (fun k => Z k ω)) atTop (𝓝 θstar) := by sorry

end LeastSquaresTD.Ergodic
