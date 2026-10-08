-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_theorem_5_2_mr
-- name    : GlobalInexactNewton.Backtracking.theorem_5_2_mr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:35:22.568865+00:00
-- url     : https://prove2.me/theorems/33a4ba62-630f-4b25-a732-586569b5dd33
-- title:
--   Theorem 5.2 (Algorithm MR) — global convergence of Algorithm MR
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F:E\to E$ continuously differentiable. Assume that Algorithm MR does not break down, producing iterates $x_k$, initial levels $\bar\eta_k$, curves $\sigma_k$ and final levels $\eta_k$. Let $x_*$ be a limit point of $(x_k)$ for which there is a constant $\Gamma$, independent of $k$, such that
--   $$\|\sigma_k(\eta)\|\le\Gamma(1-\eta)\|F(x_k)\|,\qquad\bar\eta_k\le\eta\le1, \tag{5.6}$$
--   holds whenever $x_k$ is sufficiently near $x_*$. Then $F(x_*)=0$ and $x_k\to x_*$. Furthermore, $\eta_k=\bar\eta_k$ for all sufficiently large $k$: eventually the initial level is accepted without backtracking.
--
--   No invertibility of $F'(x_*)$ is assumed. Combined with an estimate of the form (5.6) near a point where $F'$ is invertible, the theorem yields the convergence of the backtracking methods of §6.
--
--   **Formalization Note** The paper says "sufficiently near"; we state: there exist $\Gamma\in\mathbb R$ and $\delta>0$ such that (5.6) holds for every $k$ with $\|x_k-x_*\|<\delta$. Unlike (3.2), the paper does not add "for $k$ sufficiently large" here, and neither does the statement. "For all sufficiently large $k$" in the conclusion is the `atTop` filter.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 408, Theorem 5.2 (Algorithm MR)

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
open Filter Topology

namespace GlobalInexactNewton.Backtracking

/-- Eisenstat–Walker (1994), p. 408, Theorem 5.2 for Algorithm MR: assume Algorithm MR does not break
down. If `x_*` is a limit point of `{x_k}` such that there is a `Γ` independent of `k` for which
(5.6) `‖σ_k(η)‖ ≤ Γ (1 - η) ‖F(x_k)‖`, `η̄_k ≤ η ≤ 1`, holds whenever `x_k` is sufficiently near
`x_*`, then `F(x_*) = 0` and `x_k → x_*`; furthermore `η_k = η̄_k` for all sufficiently large `k`.
"Sufficiently near" is `∃ δ > 0`, after `∃ Γ`; no invertibility of `F'(x_*)` is assumed. -/
theorem theorem_5_2_mr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ)
    (σ : ℕ → ℝ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ)
    (hrun : IsMRRun F ηmax t θmin θmax x ηbar σ θ m)
    (xstar : E) (hlim : MapClusterPt xstar atTop x)
    (hΓ : ∃ Γ : ℝ, ∃ δ > 0, ∀ k, x k ∈ Metric.ball xstar δ →
      ∀ η ∈ Set.Icc (ηbar k) 1, ‖σ k η‖ ≤ Γ * (1 - η) * ‖F (x k)‖) :
    F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ᶠ k in atTop, trialLevel (ηbar k) (θ k) (m k) = ηbar k := by sorry

end GlobalInexactNewton.Backtracking
