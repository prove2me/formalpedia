-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_theorem_3_5
-- name    : GlobalInexactNewton.Backtracking.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:34:46.280486+00:00
-- url     : https://prove2.me/theorems/2060b28e-cf05-4d00-960f-5994ea935c52
-- title:
--   Theorem 3.5 — Algorithm GIN converges to a limit point near which $\|s_k\|\le\Gamma(1-\eta_k)\|F(x_k)\|$
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F:E\to E$ continuously differentiable. Assume that Algorithm GIN with parameter $t\in(0,1)$ does not break down, with iterates $x_k$, levels $\eta_k$ and steps $s_k=x_{k+1}-x_k$. Let $x_*$ be a limit point of $(x_k)$ for which there is a constant $\Gamma$, independent of $k$, with
--   $$\|s_k\|\le\Gamma(1-\eta_k)\,\|F(x_k)\| \tag{3.2}$$
--   whenever $x_k$ is sufficiently near $x_*$ and $k$ is sufficiently large. Then $x_k\to x_*$.
--
--   No invertibility of $F'(x_*)$ is assumed, and the theorem does not claim $F(x_*)=0$. It complements Theorem 3.3 and gives the convergence part of Theorem 5.2.
--
--   **Formalization Note** The paper says "sufficiently near" and "sufficiently large"; we state: there exist $\Gamma\in\mathbb R$, $\delta>0$ and $K$ such that (3.2) holds for every $k\ge K$ with $\|x_k-x_*\|<\delta$. $\Gamma$ is chosen before $k$ ("independent of $k$").
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 401, Theorem 3.5

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
open Filter Topology

namespace GlobalInexactNewton.Backtracking

/-- Eisenstat–Walker (1994), p. 401, Theorem 3.5: assume Algorithm GIN does not break down. If
`x_*` is a limit point of `{x_k}` such that there is a `Γ` independent of `k` for which (3.2)
`‖s_k‖ ≤ Γ (1 - η_k) ‖F(x_k)‖` whenever `x_k` is sufficiently near `x_*` and `k` is sufficiently
large, then `x_k → x_*`. "Sufficiently near / large" is `∃ δ > 0, ∃ K`, after `∃ Γ`. No invertibility
of `F'(x_*)` is assumed. -/
theorem theorem_3_5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (t : ℝ) (x : ℕ → E) (η : ℕ → ℝ)
    (hrun : IsGINRun F t x η) (xstar : E) (hlim : MapClusterPt xstar atTop x)
    (hΓ : ∃ Γ : ℝ, ∃ δ > 0, ∃ K : ℕ, ∀ k ≥ K, x k ∈ Metric.ball xstar δ →
      ‖x (k + 1) - x k‖ ≤ Γ * (1 - η k) * ‖F (x k)‖) :
    Tendsto x atTop (𝓝 xstar) := by sorry

end GlobalInexactNewton.Backtracking
