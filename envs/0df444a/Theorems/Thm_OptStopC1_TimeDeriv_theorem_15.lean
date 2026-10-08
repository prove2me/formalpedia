-- Prove2me | Theorems.Thm_OptStopC1_TimeDeriv_theorem_15
-- name    : OptStopC1.TimeDeriv.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:48.62138+00:00
-- url     : https://prove2.me/theorems/7141ccdb-707f-406f-af7a-5544c294aacd
-- title:
--   Theorem 15, (5.14), p. 20 — at a probabilistically regular boundary point, ∂_tV exists, equals ∂_tG, and is continuous from C
-- statement:
--   Consider the finite-horizon optimal stopping problem (2.2) for the time-space process $X^{t,x}_s=(t+s,X^x_s)$, assumed well posed (the first entry time $\tau_D$ into the stopping set is optimal). Assume:
--   1. (5.9) $V$ is continuous on $[0,T]\times\mathbb R^{d-1}$ and continuously differentiable on $C$;
--   2. (5.10) $G$ is once continuously differentiable in $t$ and twice in $x$ on $[0,T]\times\mathbb R^{d-1}$;
--   3. (5.11) $t\mapsto\tilde H(t,x):=(G_t+\mathbb L_XG+H)(t,x)$ and $t\mapsto\lambda(t,x)$ are Lipschitz on $[0,T]$, uniformly in $x$, with one constant $K>0$;
--   4. the spatial part of the process is a continuous stochastic flow in the space variable.
--
--   Let $z\in\partial C$ satisfy the local conditions (5.12) and (5.13) for some $\varepsilon>0$. If $z$ is probabilistically regular for $D^\circ$, then $\partial_tV(z)$ exists and
--   $$\partial_tV(z)=\partial_tG(z),\qquad \lim_{C\ni(t,x)\to z}\partial_tV(t,x)=\partial_tG(z).$$
--
--   This is the pointwise statement (5.14): the time derivative of the value function is continuous across the optimal stopping boundary at $z$ (smooth fit in time).
--
--   **Formalization Note** "$\partial_tV$ exists and is continuous at $z$ with $\partial_tV(z)=\partial_tG(z)$" is rendered as: $s\mapsto V(s,z_2)$ has derivative $\partial_tG(z)$ within $[0,T]$ at $z_1$, and $\partial_tV(t,x)\to\partial_tG(z)$ as $(t,x)\to z$ within $C$. Inside $D^\circ$ one has $V=G$, so this is the content of continuity at $z$. At $t=T$ the hitting window $(0,T-t]$ is empty, so no boundary point with $t=T$ is probabilistically regular, as in the paper.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, pp. 19–20, Theorem 15, (5.14)

import Mathlib
import Definitions.Def_OptStopC1_TimeDeriv_Flow
import Definitions.Def_OptStopC1_TimeDeriv_Problem
import Definitions.Def_OptStopC1_TimeDeriv_Generator
import Definitions.Def_OptStopC1_TimeDeriv_Hypotheses

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace OptStopC1.TimeDeriv

/-- Theorem 15, (5.14) (p. 20): under the hypotheses of Theorem 15 at a boundary point `z ∈ ∂C`
that is probabilistically regular for `D°`, `∂_tV(z)` exists and equals `∂_tG(z)`, and
`∂_tV(t, x) → ∂_tG(z)` as `C ∋ (t, x) → z`. -/
theorem theorem_15 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : StoppingProblem m Ω) (c : GenCoeffs m)
    (hM : M.Thm15Global c) (z : ℝ × Space m) (hz : z ∈ M.boundary)
    (hloc : M.Thm15AtPoint c z)
    (hPR : IsProbRegular M.P M.T M.X (interior M.stoppingSet) z) :
    HasDerivWithinAt (fun s => M.value (s, z.2)) (timeDeriv M.T M.G z) (Set.Icc 0 M.T) z.1 ∧
    Tendsto (timeDeriv M.T M.value) (𝓝[M.contSet] z) (𝓝 (timeDeriv M.T M.G z)) := by sorry

end OptStopC1.TimeDeriv
