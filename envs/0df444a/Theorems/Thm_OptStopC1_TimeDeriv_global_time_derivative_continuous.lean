-- Prove2me | Theorems.Thm_OptStopC1_TimeDeriv_global_time_derivative_continuous
-- name    : OptStopC1.TimeDeriv.global_time_derivative_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:34:03.89725+00:00
-- url     : https://prove2.me/theorems/a7af9298-a80d-4967-accd-1f1264143bff
-- title:
--   Theorem 15, p. 20 — if the hypotheses hold at every z ∈ ∂C, then ∂_tV is continuous on [0, T] × ℝ^{d−1}
-- statement:
--   Consider the finite-horizon optimal stopping problem
--   $$V(t,x)=\sup_{0\le\tau\le T-t}\mathsf E\Big[e^{-\Lambda^{t,x}_\tau}G(t+\tau,X^x_\tau)+\int_0^\tau e^{-\Lambda^{t,x}_s}H(t+s,X^x_s)\,ds\Big]$$
--   for the time-space process $X^{t,x}_s=(t+s,X^x_s)$, where $X^x$ is a càdlàg strong Markov flow in $\mathbb R^{d-1}$ and $\Lambda^{t,x}_s=\int_0^s\lambda(t+u,X^x_u)\,du$. Assume the problem is well posed, so that the first entry time $\tau_D$ into the stopping set $D=\{V=G\}$ is optimal. Assume also:
--   1. (5.9) $V$ is continuous on $[0,T]\times\mathbb R^{d-1}$ and continuously differentiable on the continuation set $C=\{V>G\}$;
--   2. (5.10) $G$ is once continuously differentiable in $t$ and twice in $x$;
--   3. (5.11) $\tilde H=G_t+\mathbb L_XG+H$ and $\lambda$ are Lipschitz in $t$ on $[0,T]$, uniformly in $x$;
--   4. the flow is continuous in the space variable.
--
--   Suppose that at **every** boundary point $z\in\partial C$ the local conditions (5.12)–(5.13) hold and $z$ is probabilistically regular for $D^\circ$. Then $\partial_tV$ exists at every point of $[0,T]\times\mathbb R^{d-1}$ and
--   $$\partial_tV\ \text{is continuous on }[0,T]\times\mathbb R^{d-1}.$$
--
--   This is the global form of the continuity of the time derivative of the value function in finite horizon: probabilistic regularity of the optimal stopping boundary yields the smooth fit in time everywhere.
--
--   **Formalization Note** $\partial_tV(t,x)$ is the derivative of $s\mapsto V(s,x)$ within $[0,T]$, one-sided at $t=0$ and $t=T$. No boundary point with $t=T$ is probabilistically regular (the hitting window $(0,T-t]$ is empty there). So the hypothesis at every $z\in\partial C$ requires $\overline C$ not to meet $\{T\}\times\mathbb R^{d-1}$; this is the paper's own scope, and the American put of Example 17 is treated separately in the paper.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, pp. 19–20, Theorem 15, last sentence

import Mathlib
import Definitions.Def_OptStopC1_TimeDeriv_Flow
import Definitions.Def_OptStopC1_TimeDeriv_Problem
import Definitions.Def_OptStopC1_TimeDeriv_Generator
import Definitions.Def_OptStopC1_TimeDeriv_Hypotheses

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace OptStopC1.TimeDeriv

/-- Theorem 15, last sentence (p. 20): if the hypotheses of Theorem 15 hold at every `z ∈ ∂C`,
including probabilistic regularity of `z` for `D°`, then `∂_tV` exists and is continuous on
`[0, T] × ℝ^{d−1}`. -/
theorem global_time_derivative_continuous {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : StoppingProblem m Ω) (c : GenCoeffs m)
    (hM : M.Thm15Global c)
    (hloc : ∀ z ∈ M.boundary, M.Thm15AtPoint c z)
    (hPR : ∀ z ∈ M.boundary, IsProbRegular M.P M.T M.X (interior M.stoppingSet) z) :
    (∀ p ∈ domain m M.T,
      DifferentiableWithinAt ℝ (fun s => M.value (s, p.2)) (Set.Icc 0 M.T) p.1) ∧
    ContinuousOn (timeDeriv M.T M.value) (domain m M.T) := by sorry

end OptStopC1.TimeDeriv
