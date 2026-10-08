-- Prove2me | Theorems.Thm_GlobalInexactNewton_TrustRegion_corollary_3_7
-- name    : GlobalInexactNewton.TrustRegion.corollary_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:10.046679+00:00
-- url     : https://prove2.me/theorems/f23660dc-2af8-4a43-9384-bf4dd7715bb7
-- title:
--   Corollary 3.7 — a sequence with pred ≥ 0, ared ≥ t·pred and ‖s_k‖ ≤ Γ·pred near a limit point converges to it
-- statement:
--   Let $E$ be a finite-dimensional real space with an arbitrary norm, and let $F:E\to E$ be continuously differentiable. Let $(x_k)_{k\ge0}$ be any sequence in $E$, write $s_k = x_{k+1}-x_k$, and let $\operatorname{ared}_k$, $\operatorname{pred}_k$ be the actual and predicted reductions (2.4) at $x_k$. Assume that for some $t\in(0,1)$ independent of $k$,
--   $$\operatorname{pred}_k(s_k)\ge 0\quad\text{and}\quad \operatorname{ared}_k(s_k)\ge t\cdot\operatorname{pred}_k(s_k)\qquad\text{for each }k.$$
--   Let $x_*$ be a limit point of $(x_k)$, and suppose there is a $\Gamma$ independent of $k$ such that
--   $$\|s_k\|\le\Gamma\cdot\operatorname{pred}_k(s_k)$$
--   whenever $x_k$ is sufficiently near $x_*$ and $k$ is sufficiently large. Then $x_k\to x_*$.
--
--   No invertibility of $F'(x_*)$ is assumed. This is the restatement of Theorem 3.5 for arbitrary sequences whose steps do not increase the norm of the local linear model, and it is the tool from which the paper derives the convergence part of Lemma 4.1 for Algorithm TR.
--
--   **Formalization Note.** "Limit point" (p. 396: every neighbourhood contains $x_k$ for infinitely many $k$) is `MapClusterPt xstar atTop x`. The paper states "whenever $x_k$ is sufficiently near $x_*$ and $k$ is sufficiently large"; we state: there exist $\Gamma\in\mathbf R$, $\rho>0$ and $K$ such that the bound holds for every $k\ge K$ with $\|x_k-x_*\|<\rho$.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 402, Corollary 3.7

import Mathlib
import Definitions.Def_GlobalInexactNewton_TrustRegion_Method

namespace GlobalInexactNewton.TrustRegion

open Filter Topology

/-- Corollary 3.7, p. 402. -/
theorem corollary_3_7 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : ℕ → E)
    (hpred : ∀ k, 0 ≤ GlobalInexactNewton.Backtracking.pred F (x k) (x (k + 1) - x k))
    (hared : ∀ k, t * GlobalInexactNewton.Backtracking.pred F (x k) (x (k + 1) - x k) ≤ GlobalInexactNewton.Backtracking.ared F (x k) (x (k + 1) - x k))
    (xstar : E) (hlim : MapClusterPt xstar atTop x)
    (hΓ : ∃ Γ : ℝ, ∃ ρ > 0, ∃ K : ℕ, ∀ k ≥ K, x k ∈ Metric.ball xstar ρ →
      ‖x (k + 1) - x k‖ ≤ Γ * GlobalInexactNewton.Backtracking.pred F (x k) (x (k + 1) - x k)) :
    Tendsto x atTop (𝓝 xstar) := by sorry

end GlobalInexactNewton.TrustRegion
