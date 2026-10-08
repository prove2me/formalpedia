-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_theorem_3_3
-- name    : GlobalInexactNewton.Backtracking.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:34:13.242915+00:00
-- url     : https://prove2.me/theorems/4d15d9b0-5d6b-42ef-9a00-22f645705eb4
-- title:
--   Theorem 3.3 — if $F(x_k)\to0$, $\|F(x_k)\|$ is nonincreasing and the steps are inexact Newton steps at a fixed level, a limit point with $F'$ invertible is a zero and the limit
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F:E\to E$ continuously differentiable. Let $(x_k)_{k\ge0}$ be a sequence in $E$ and $\eta$ a real number independent of $k$, and write $s_k=x_{k+1}-x_k$. Assume that $F(x_k)\to0$ and that for every $k$
--   $$\|F(x_k)+F'(x_k)s_k\|\le\eta\,\|F(x_k)\|\qquad\text{and}\qquad\|F(x_{k+1})\|\le\|F(x_k)\|.$$
--   If $x_*$ is a limit point of $(x_k)$ such that $F'(x_*)$ is invertible, then $F(x_*)=0$ and $x_k\to x_*$.
--
--   The theorem is not tied to any algorithm: the inexact Newton condition with a uniform level keeps the steps proportional to the residual near $x_*$, which prevents the iterates from wandering away from a limit point. It gives the second half of Theorem 3.4.
--
--   **Formalization Note** "$x_*$ is a limit point" (for every $\delta>0$, infinitely many $x_k$ lie in $N_\delta(x_*)$) is `MapClusterPt xstar atTop x`. The paper gives $\eta$ no range, and neither does the statement.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), pp. 398–399, Theorem 3.3

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
open Filter Topology

namespace GlobalInexactNewton.Backtracking

/-- Eisenstat–Walker (1994), pp. 398–399, Theorem 3.3: let `{x_k}` be a sequence with
`F(x_k) → 0` and, for each `k`, `‖F(x_k) + F'(x_k) s_k‖ ≤ η ‖F(x_k)‖` and
`‖F(x_{k+1})‖ ≤ ‖F(x_k)‖`, where `s_k = x_{k+1} - x_k` and `η` is independent of `k`. If `x_*` is a
limit point of `{x_k}` with `F'(x_*)` invertible, then `F(x_*) = 0` and `x_k → x_*`. -/
theorem theorem_3_3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (x : ℕ → E) (η : ℝ)
    (hF0 : Tendsto (fun k => F (x k)) atTop (𝓝 0))
    (hinexact : ∀ k, InexactNewtonCond F (x k) (x (k + 1) - x k) η)
    (hmono : ∀ k, ‖F (x (k + 1))‖ ≤ ‖F (x k)‖)
    (xstar : E) (hlim : MapClusterPt xstar atTop x) (hinv : (fderiv ℝ F xstar).IsInvertible) :
    F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) := by sorry

end GlobalInexactNewton.Backtracking
