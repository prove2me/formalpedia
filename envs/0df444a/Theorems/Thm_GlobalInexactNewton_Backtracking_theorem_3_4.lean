-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_theorem_3_4
-- name    : GlobalInexactNewton.Backtracking.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:34:14.731106+00:00
-- url     : https://prove2.me/theorems/5a9925d3-5e90-41a4-bb72-85a011f8d0a7
-- title:
--   Theorem 3.4 — global convergence of Algorithm GIN
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F:E\to E$ continuously differentiable. Assume that Algorithm GIN with parameter $t\in(0,1)$ does not break down, producing iterates $x_k$ and levels $\eta_k\in[0,1)$ such that $s_k=x_{k+1}-x_k$ satisfies (2.1) and (2.2). If
--   $$\sum_{k\ge0}(1-\eta_k)=\infty,$$
--   then $F(x_k)\to0$. If, in addition, $x_*$ is a limit point of $(x_k)$ such that $F'(x_*)$ is invertible, then $F(x_*)=0$ and $x_k\to x_*$.
--
--   This is the basic global convergence theorem for the framework: every later algorithm (MR, TL, INB, ENB) is shown to be a special case of GIN, and its convergence result is derived from this theorem and Theorem 3.5.
--
--   **Formalization Note** The terms $1-\eta_k$ are positive, so divergence of the series is stated as "not summable". "Does not break down" is the run predicate `IsGINRun`. A limit point is `MapClusterPt`.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 400, Theorem 3.4

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
open Filter Topology

namespace GlobalInexactNewton.Backtracking

/-- Eisenstat–Walker (1994), p. 400, Theorem 3.4 (global convergence of Algorithm GIN): assume
Algorithm GIN does not break down. If `∑_{k ≥ 0} (1 - η_k)` is divergent, then `F(x_k) → 0`. If, in
addition, `x_*` is a limit point of `{x_k}` with `F'(x_*)` invertible, then `F(x_*) = 0` and
`x_k → x_*`. The terms `1 - η_k` are positive, so divergence is `¬ Summable`. -/
theorem theorem_3_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (t : ℝ) (x : ℕ → E) (η : ℕ → ℝ)
    (hrun : IsGINRun F t x η) (hdiv : ¬ Summable (fun k => 1 - η k)) :
    Tendsto (fun k => F (x k)) atTop (𝓝 0) ∧
      ∀ xstar : E, MapClusterPt xstar atTop x → (fderiv ℝ F xstar).IsInvertible →
        F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) := by sorry

end GlobalInexactNewton.Backtracking
