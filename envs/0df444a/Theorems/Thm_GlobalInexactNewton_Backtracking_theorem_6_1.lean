-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_theorem_6_1
-- name    : GlobalInexactNewton.Backtracking.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:36:24.819986+00:00
-- url     : https://prove2.me/theorems/ae2a2287-55dc-413b-b6eb-9a85550cd8bd
-- title:
--   Theorem 6.1 — global convergence of Algorithm INB
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F:E\to E$ continuously differentiable. Assume that Algorithm INB, with parameters $\eta_{\max}\in[0,1)$, $t\in(0,1)$ and $0<\theta_{\min}<\theta_{\max}<1$, does not break down. Iteration $k$ chooses $\bar\eta_k\in[0,\eta_{\max}]$ and an inexact Newton step $\bar s_k$ with $\|F(x_k)+F'(x_k)\bar s_k\|\le\bar\eta_k\|F(x_k)\|$, and backtracks $s_k\leftarrow\theta s_k$, $\eta_k\leftarrow1-\theta(1-\eta_k)$ until
--   $$\|F(x_k+s_k)\|\le[1-t(1-\eta_k)]\,\|F(x_k)\|;$$
--   then $x_{k+1}=x_k+s_k$.
--
--   If $x_*$ is a limit point of $(x_k)$ such that $F'(x_*)$ is invertible, then
--   $$F(x_*)=0\qquad\text{and}\qquad x_k\to x_*.$$
--   Furthermore, $s_k=\bar s_k$ and $\eta_k=\bar\eta_k$ for all sufficiently large $k$: eventually the initial inexact Newton step is accepted without backtracking.
--
--   The last clause means that, near a solution, the local convergence rate of the method is governed by the choice of initial levels $\bar\eta_k$, as in the local theory of inexact Newton methods.
--
--   **Formalization Note** "Does not break down" is the run predicate `IsINBRun`: the run is an infinite sequence, and every while-loop exits after finitely many passes $m_k$. $s_k$ and $\eta_k$ are the values on exit from the loop. A limit point is `MapClusterPt`, and invertibility of $F'(x_*)$ is `ContinuousLinearMap.IsInvertible`.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 410, Theorem 6.1

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
open Filter Topology

namespace GlobalInexactNewton.Backtracking

/-- Eisenstat–Walker (1994), p. 410, Theorem 6.1 (global convergence of Algorithm INB): assume
Algorithm INB does not break down. If `x_*` is a limit point of `{x_k}` such that `F'(x_*)` is
invertible, then `F(x_*) = 0` and `x_k → x_*`. Furthermore, `s_k = s̄_k` and `η_k = η̄_k` for all
sufficiently large `k`, where `s_k = trialStep (sbar k) (θ k) (m k)` and
`η_k = trialLevel (ηbar k) (θ k) (m k)` are the values on exit from the while-loop. -/
theorem theorem_6_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ)
    (sbar : ℕ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ)
    (hrun : IsINBRun F ηmax t θmin θmax x ηbar sbar θ m)
    (xstar : E) (hlim : MapClusterPt xstar atTop x) (hinv : (fderiv ℝ F xstar).IsInvertible) :
    F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ᶠ k in atTop, trialStep (sbar k) (θ k) (m k) = sbar k ∧
        trialLevel (ηbar k) (θ k) (m k) = ηbar k := by sorry

end GlobalInexactNewton.Backtracking
