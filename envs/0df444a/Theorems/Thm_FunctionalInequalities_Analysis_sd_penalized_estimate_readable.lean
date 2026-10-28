-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sd_penalized_estimate_readable
-- name    : FunctionalInequalities.Analysis.sd_penalized_estimate_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:50.726093+00:00
-- url     : https://prove2.me/theorems/c0c70d58-7455-4740-861b-7db419ae03b7
-- title:
--   Penalized Maximum Second-Difference Estimate
-- statement:
--   This is a technical estimate at a penalized maximum of a convex function's second difference.
--
--   Let $E$ be finite-dimensional, let $u,V:E\to\mathbb R$ be differentiable, let $u$ be convex, and let $\kappa>0$. Assume that $V(y)-\frac\kappa2\|y\|^2$ is convex. Suppose there is $C\in\mathbb R$ such that
--
--   $$
--   \left|D V(\nabla u(x))[\nabla u(x)]\right|\leq C
--   $$
--
--   for every $x$. For $\eta>0$, $x_0,h\in E$, assume that the penalized second difference at $x_0$ dominates that at every $y$, and that the corresponding comparison for $V\circ\nabla u-u$ is at most $\eta n$. Then
--
--   $$
--   \Delta_h^2u(x_0)
--   \leq
--   \frac{4\|h\|^2}{\kappa}
--   +2\|h\|\sqrt{\frac{\eta(n+C)}{\kappa}},
--   $$
--
--   where $\Delta_h^2u(x)=u(x+h)+u(x-h)-2u(x)$. This auxiliary estimate is the algebraic maximum-principle step before letting $\eta\downarrow0$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 800000 in
--   private lemma sd_penalized_estimate {u V : E → ℝ}
--       (hconv : ConvexOn ℝ univ u) (hu : Differentiable ℝ u)
--       (hV : Differentiable ℝ V) {κ : ℝ} (hκ : 0 < κ)
--       (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
--       {C : ℝ} (hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C)
--       (n : ℕ) (h x₀ : E) {η : ℝ} (hη : 0 < η)
--       (hmaximum : ∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
--         u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀)
--       (hcomparison :
--         (V (gradient u (x₀ + h)) - u (x₀ + h)) +
--           (V (gradient u (x₀ - h)) - u (x₀ - h)) -
--           2 * (V (gradient u x₀) - u x₀) ≤ η * n) :
--       u (x₀ + h) + u (x₀ - h) - 2 * u x₀ ≤
--         4 * ‖h‖ ^ 2 / κ + 2 * ‖h‖ * Real.sqrt (η * (n + C) / κ)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/SecondDifference`](https://prove2.me/theorems/5412cb80-13f4-48d5-ab21-d4aec90af26d).
--
--   Previous: [`lipschitzWith_gradient_of_second_difference_le`](https://prove2.me/theorems/b83dfd5c-be3e-4ba7-94af-eada55e6bd84) · Next: [`secondDifference_le_of_penalized_maxima`](https://prove2.me/theorems/a468a648-0c26-4aab-8d67-0b4ddb3e936a).
--
--   [Source excerpt, lines 586–600](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L586-L600) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L586-L685 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondDifference`, declaration `_private.FunctionalInequalities.Analysis.Convex.SecondDifference.0.FunctionalInequalities.Analysis.sd_penalized_estimate`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondDifference

open Set
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
set_option maxHeartbeats 800000

lemma FunctionalInequalities.Analysis.sd_penalized_estimate_readable {u V : E → ℝ}
    (hconv : ConvexOn ℝ univ u) (hu : Differentiable ℝ u)
    (hV : Differentiable ℝ V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    {C : ℝ} (hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C)
    (n : ℕ) (h x₀ : E) {η : ℝ} (hη : 0 < η)
    (hmaximum : ∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
      u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀)
    (hcomparison :
      (V (gradient u (x₀ + h)) - u (x₀ + h)) +
        (V (gradient u (x₀ - h)) - u (x₀ - h)) -
        2 * (V (gradient u x₀) - u x₀) ≤ η * n) :
    u (x₀ + h) + u (x₀ - h) - 2 * u x₀ ≤
      4 * ‖h‖ ^ 2 / κ + 2 * ‖h‖ * Real.sqrt (η * (n + C) / κ) := by sorry
