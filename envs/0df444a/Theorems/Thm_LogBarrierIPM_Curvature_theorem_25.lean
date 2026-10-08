-- Prove2me | Theorems.Thm_LogBarrierIPM_Curvature_theorem_25
-- name    : LogBarrierIPM.Curvature.theorem_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:40.730726+00:00
-- url     : https://prove2.me/theorems/7aedf070-f185-41f8-b407-57168b46e1f0
-- title:
--   Theorem 25 — the total curvature of the central path of $\mathrm{LW}^=_r(t)$ exceeds $(2^{r-2}-1)\pi/2-\epsilon$ for all large $t$
-- statement:
--   Let $r\ge1$ and consider the linear program $\mathrm{LW}^=_r(t)=\mathrm{LP}(A,b,c)$ in slack form, with $n=2r$ variables, $3r-1$ slack variables and $N=5r-1$. For $t>0$ let $\mu\mapsto(x^\mu,w^\mu,s^\mu,y^\mu)$, $\mu>0$, be its primal-dual central path (the solution of system (1)), and $\mu\mapsto(x^\mu,w^\mu)\in\mathbb R^N$ its primal central path.
--
--   **Theorem.** For every $\epsilon>0$ there is $t_0$ such that for every $t>t_0$ the total curvature of the primal central path of $\mathrm{LW}^=_r(t)$ satisfies
--   $$\kappa\big(\mu\mapsto(x^\mu,w^\mu),\ (0,\infty)\big)\ >\ \big(2^{r-2}-1\big)\frac\pi2-\epsilon,$$
--   and the same holds for the primal-dual central path $\mu\mapsto(x^\mu,w^\mu,s^\mu,y^\mu)\in\mathbb R^{2N}$.
--
--   Since $\mathrm{LW}_r(t)$ has $2r$ variables and $3r+1$ constraints, the total curvature of its central path is exponential in the number of constraints. This disproves the "continuous analogue of the Hirsch conjecture" of Deza, Terlaky and Zinchenko, which asks for a bound linear in the number of constraints.
--
--   **Formalization Note** $t_0$ depends on $r$ and $\epsilon$. The central path is any function $C$ with $C(\mu)$ solving system (1) for every $\mu>0$; system (1) has exactly one solution for each $\mu>0$ (the referenced item `VanderbeiLP.CentralPath.central_path_exists_unique`, for objective $-c$, applies since $\mathrm{LW}_r(t)$ is strictly feasible and bounded), so this is the central path. Total curvature is the `EReal` supremum over polygons inscribed over $\mu\in(0,\infty)$, with turning angles in Euclidean space. $2^{r-2}$ is an integer power of the real $2$ (so it is $1/2$ for $r=1$); for $r\le2$ the bound is negative and the statement holds trivially, as in the paper.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 22, Theorem 25 (= Theorem A, p. 2)

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_TotalCurvature
import Definitions.Def_LogBarrierIPM_Curvature_SlackCentralPath
import Definitions.Def_LogBarrierIPM_Iterations_LW

namespace LogBarrierIPM.Curvature

/-- Theorem 25 (p. 22). For every `r ≥ 1` and `ε > 0` there is `t₀` such that for every `t > t₀`,
the total curvature of the primal central path of `LW^=_r(t)` over `μ ∈ (0, ∞)`, and that of its
primal-dual central path, both exceed `(2^{r−2} − 1) π/2 − ε`. -/
theorem theorem_25 (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ t₀ : ℝ, ∀ t : ℝ, t₀ < t →
      ∀ C : ℝ → SlackPoint (2 * r) (3 * r - 1),
        (∀ μ : ℝ, 0 < μ → IsSlackCentralPathPoint (LogBarrierIPM.Iterations.lwA r t) (LogBarrierIPM.Iterations.lwB r t) (LogBarrierIPM.Iterations.lwC r) μ (C μ)) →
        ((((2 : ℝ) ^ ((r : ℤ) - 2) - 1) * Real.pi / 2 - ε : ℝ) : EReal) <
            totalCurvature (fun μ => primalPoint (C μ)) (Set.Ioi 0) ∧
          ((((2 : ℝ) ^ ((r : ℤ) - 2) - 1) * Real.pi / 2 - ε : ℝ) : EReal) <
            totalCurvature (fun μ => primalDualPoint (C μ)) (Set.Ioi 0) := by sorry

end LogBarrierIPM.Curvature
