-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_lemma_5_1
-- name    : GlobalInexactNewton.Backtracking.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:34:33.73498+00:00
-- url     : https://prove2.me/theorems/c36c53e1-3feb-43b2-a64c-85a67ed12bc4
-- title:
--   Lemma 5.1 — the while-loop of Algorithms MR and TL terminates, with $1-\eta_k\ge\min\{1-\bar\eta_k,\theta_{\min}\delta/(\Gamma\|F(x_k)\|)\}$
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F:E\to E$ continuously differentiable. Fix $t\in(0,1)$ and $0<\theta_{\min}<\theta_{\max}<1$, and consider the $k$th iteration of Algorithm MR or Algorithm TL: a current iterate $x_k$, an initial level $\bar\eta_k\in[0,1)$ and a curve $\sigma_k$ satisfying (5.1) on $[\bar\eta_k,1]$. The while-loop starts at $\eta_k=\bar\eta_k$ and, as long as $\|F(x_k+\sigma_k(\eta_k))\|>[1-t(1-\eta_k)]\|F(x_k)\|$, replaces $\eta_k$ by $1-\theta(1-\eta_k)$ for some $\theta\in[\theta_{\min},\theta_{\max}]$.
--
--   Assume $F(x_k)\ne0$ and that there is $\Gamma$ with
--   $$\|\sigma_k(\eta)\|\le\Gamma(1-\eta)\|F(x_k)\|,\qquad\bar\eta_k\le\eta\le1. \tag{5.3}$$
--   Then, whatever factors $\theta$ the loop chooses:
--
--   1. the while-loop terminates;
--   2. on termination,
--   $$1-\eta_k\ge\min\left\{1-\bar\eta_k,\ \frac{\theta_{\min}\delta}{\Gamma\|F(x_k)\|}\right\} \tag{5.4}$$
--   for every $\delta>0$ small enough that
--   $$\|F(x)-F(x_k)-F'(x_k)(x-x_k)\|\le\frac{1-t}{\Gamma}\|x-x_k\|\quad\text{whenever }\|x-x_k\|<\delta. \tag{5.5}$$
--
--   The lemma says when neither algorithm breaks down inside the while-loop, and the lower bound (5.4) on $1-\eta_k$ is what makes $\sum_k(1-\eta_k)$ diverge in Theorem 5.2.
--
--   **Formalization Note** The while-loop is identical in MR and TL, so the lemma is stated once for a single iteration, which covers both. The factors are an arbitrary sequence $\theta_0,\theta_1,\dots$ in $[\theta_{\min},\theta_{\max}]$, and $\eta^{(j)}$ are the levels the loop visits. "Terminates" is: some index $m$ passes (2.2) while every $j<m$ fails it. Part 2 is stated for every such exit index $m$. The hypotheses force $\Gamma>0$ (at $\eta=\bar\eta_k$, (5.1) and (5.3) are incompatible with $\Gamma\le0$ when $F(x_k)\ne0$), so the divisions by $\Gamma$ are genuine.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 408, Lemma 5.1

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
open Filter Topology

namespace GlobalInexactNewton.Backtracking

/-- Eisenstat–Walker (1994), p. 408, Lemma 5.1, for one iteration of the while-loop shared by
Algorithms MR and TL. Data: `t ∈ (0,1)`, `0 < θ_min < θ_max < 1`, the current iterate `x_k`, an
initial level `η̄_k ∈ [0,1)`, a curve `σ_k` with (5.1) on `[η̄_k, 1]`, and an arbitrary choice of
factors `θ_j ∈ [θ_min, θ_max]`. If `F(x_k) ≠ 0` and `Γ` satisfies (5.3)
`‖σ_k(η)‖ ≤ Γ (1 - η) ‖F(x_k)‖` on `[η̄_k, 1]`, then the while-loop terminates (some trial passes (2.2)
after all earlier trials failed), and at termination (5.4)
`1 - η_k ≥ min {1 - η̄_k, θ_min δ / (Γ ‖F(x_k)‖)}` for every `δ > 0` with (5.5)
`‖F(x) - F(x_k) - F'(x_k)(x - x_k)‖ ≤ ((1 - t)/Γ) ‖x - x_k‖` on `N_δ(x_k)`. -/
theorem lemma_5_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (t θmin θmax : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hθ : 0 < θmin ∧ θmin < θmax ∧ θmax < 1)
    (xk : E) (ηbar : ℝ) (hηbar : ηbar ∈ Set.Ico (0 : ℝ) 1) (σ : ℝ → E)
    (hσ : ∀ η ∈ Set.Icc ηbar 1, InexactNewtonCond F xk (σ η) η)
    (hFxk : F xk ≠ 0) (Γ : ℝ) (hΓ : ∀ η ∈ Set.Icc ηbar 1, ‖σ η‖ ≤ Γ * (1 - η) * ‖F xk‖)
    (θ : ℕ → ℝ) (hθmem : ∀ j, θ j ∈ Set.Icc θmin θmax) :
    (∃ m : ℕ, (∀ j < m, ¬ SuffDecrease F t xk (σ (trialLevel ηbar θ j)) (trialLevel ηbar θ j)) ∧
        SuffDecrease F t xk (σ (trialLevel ηbar θ m)) (trialLevel ηbar θ m)) ∧
      ∀ m : ℕ, (∀ j < m, ¬ SuffDecrease F t xk (σ (trialLevel ηbar θ j)) (trialLevel ηbar θ j)) →
        SuffDecrease F t xk (σ (trialLevel ηbar θ m)) (trialLevel ηbar θ m) →
        ∀ δ > 0, (∀ y ∈ Metric.ball xk δ,
            ‖F y - F xk - fderiv ℝ F xk (y - xk)‖ ≤ (1 - t) / Γ * ‖y - xk‖) →
          min (1 - ηbar) (θmin * δ / (Γ * ‖F xk‖)) ≤ 1 - trialLevel ηbar θ m := by sorry

end GlobalInexactNewton.Backtracking
