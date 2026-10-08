-- Prove2me | Theorems.Thm_GlobalInexactNewton_TrustRegion_lemma_4_1
-- name    : GlobalInexactNewton.TrustRegion.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:08.739975+00:00
-- url     : https://prove2.me/theorems/fd5b86e4-4c0d-4baf-98b7-1cf9ef91340b
-- title:
--   Lemma 4.1 — if (4.1) holds near a limit point of Algorithm TR, then x_k → x* and liminf δ_k > 0
-- statement:
--   Let $E$ be a finite-dimensional real space with an arbitrary norm, let $F:E\to E$ be continuously differentiable, and consider a run of Algorithm TR (trust region method) with parameters $\bar\delta_0>0$, $0<t\le u<1$, $0<\theta_{\min}<\theta_{\max}<1$, iterates $x_k$, accepted steps $s_k$ and final trust region radii $\delta_k$. Suppose that $x_*$ is a limit point of $(x_k)$ such that there exists a $\Gamma$ independent of $k$ for which
--   $$\|s_k\|\le\Gamma\cdot\operatorname{pred}_k(s_k)\tag{4.1}$$
--   holds for every step $s_k$ computed at iteration $k$ (every trial step of the while-loop, including the accepted one) whenever $x_k$ is sufficiently near $x_*$ and $k$ is sufficiently large. Then
--   $$x_k\to x_*\qquad\text{and}\qquad\liminf_{k\to\infty}\delta_k>0.$$
--
--   This lemma isolates the two consequences of (4.1) that Theorem 4.4 needs: convergence of the iterates, and trust region radii that stay bounded away from zero.
--
--   **Formalization Note.** The paper states (4.1) for $s_k$, the variable of Algorithm TR that takes the value of every trial step $s_{k,0},\dots,s_{k,m_k}$ of iteration $k$, and its proof on p. 403 applies (4.1) to trial steps; we state (4.1) for every trial step $s_{k,j}$, $j\le m_k$. (Requiring it only for the accepted step $s_{k,m_k}$ would make the lemma false: for $F(x)=1+x^2$ on $\mathbf R$ and $x_k=0$, a run may reject a nonzero trial step at every iteration and accept $s_k=0$, so (4.1) holds for accepted steps while $\delta_k\to0$.) "Sufficiently near/large" is: there exist $\Gamma\in\mathbf R$, $\rho>0$ and $K$ such that (4.1) holds whenever $k\ge K$ and $\|x_k-x_*\|<\rho$. "$\liminf\delta_k>0$" (possibly $+\infty$) is stated as: there is $c>0$ with $\delta_k\ge c$ for all sufficiently large $k$, which is equivalent for a real sequence and avoids the junk value of `Filter.liminf` on unbounded sequences. "Algorithm TR does not break down" is the run hypothesis.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 403, Lemma 4.1, (4.1)

import Mathlib
import Definitions.Def_GlobalInexactNewton_TrustRegion_Method

namespace GlobalInexactNewton.TrustRegion

open Filter Topology

/-- Lemma 4.1, p. 403. In Algorithm TR, `s_k` is the loop variable of iteration `k`: it takes the
value of every trial step `s k j`, `j ≤ m k`, and the proof on p. 403 applies (4.1) to trial steps.
So (4.1) is required for every trial step of an iteration with `x_k` near `x*` and `k` large. -/
theorem lemma_4_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (t u θmin θmax : ℝ) (x : ℕ → E) (δbar : ℕ → ℝ)
    (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (s : ℕ → ℕ → E)
    (hrun : IsTRRun F t u θmin θmax x δbar θ m s)
    (xstar : E) (hlim : MapClusterPt xstar atTop x)
    (hΓ : ∃ Γ : ℝ, ∃ ρ > 0, ∃ K : ℕ, ∀ k ≥ K, x k ∈ Metric.ball xstar ρ → ∀ j ≤ m k,
      ‖s k j‖ ≤ Γ * GlobalInexactNewton.Backtracking.pred F (x k) (s k j)) :
    Tendsto x atTop (𝓝 xstar) ∧
      ∃ c > (0 : ℝ), ∀ᶠ k in atTop, c ≤ trialRadius (δbar k) (θ k) (m k) := by sorry

end GlobalInexactNewton.TrustRegion
