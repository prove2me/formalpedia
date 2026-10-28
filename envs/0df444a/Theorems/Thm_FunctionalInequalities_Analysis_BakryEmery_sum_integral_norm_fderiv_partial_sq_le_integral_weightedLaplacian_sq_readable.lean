-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:46.491504+00:00
-- url     : https://prove2.me/theorems/34cc3097-b38d-4f33-9bd3-39c1af8e4e9d
-- title:
--   Coordinate Hessian Bound for a Convex Potential
-- statement:
--   This is the coordinate form of the Bochner bound cited as Proposition 2.8 of Letwin (arXiv:2607.24164v1).
--
--   Let $n\in\mathbb N$, let $m$ be an additive Haar measure on $\mathbb R^n\simeq\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))$, and let $W$ be a $C^2$ convex function. Let $g$ be smooth and compactly supported. With $\mu=m.\operatorname{tilted}(-W)$ and $e_i$ the standard coordinate vectors,
--
--   $$\sum_{i=1}^n\int\left\|D\bigl(x\mapsto Dg(x)[e_i]\bigr)\right\|^2\,d\mu(x)
--   \le\int\bigl(\operatorname{weightedLaplacian}(W,g)(x)\bigr)^2\,d\mu(x).$$
--
--   This is a finite-dimensional coordinate version of the integrated Hessian estimate and is used in dual-gradient and $H^{-1}$ arguments.
--
--   **Formalization Note.** The ambient space is exactly `EuclideanSpace ℝ (Fin n)`; no positivity assumption on $n$ is included.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq [m.IsAddHaarMeasure]
--       {W : EuclideanSpace ℝ (Fin n) → ℝ} (hW : ContDiff ℝ 2 W) (hWc : ConvexOn ℝ Set.univ W)
--       {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
--       ∑ i, ∫ x, ‖fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2
--           ∂(m.tilted (-W)) ≤
--         ∫ x, weightedLaplacian W g x ^ 2 ∂(m.tilted (-W))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HminusOne`](https://prove2.me/theorems/4dc71c7a-51b5-45a0-8de3-41cf287dbc05).
--
--   Definition modules: [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Supporting theorems: [`gammaTwo_eq_hessianSqStdBasis_add`](https://prove2.me/theorems/179f18c6-eedc-4764-b606-7f97a6d4c71b), [`integrable_gamma_weightedLaplacian`](https://prove2.me/theorems/81349000-218c-4632-9392-38a80df79038), [`integrable_weightedLaplacian_gamma`](https://prove2.me/theorems/59b753c1-8f58-4542-b8fb-6fd46908e479), [`integral_gamma_weightedLaplacian_eq`](https://prove2.me/theorems/ad0e7a85-df83-4e4f-b668-268c7893adec).
--
--   Previous: [`nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq`](https://prove2.me/theorems/b98a51cc-c659-42c7-9c41-59b73de13a36) · Next: [`variance_le_sum_of_partial_dual_bounds`](https://prove2.me/theorems/87d34084-ab4b-4b3e-96bf-c24d3921e663).
--
--   [Source excerpt, lines 264–269](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean#L264-L269) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean#L259-L432 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HminusOne`, declaration `FunctionalInequalities.Analysis.BakryEmery.sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HminusOne

open scoped ContDiff
variable {n : ℕ}
variable (m : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))

theorem FunctionalInequalities.Analysis.BakryEmery.sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq_readable [m.IsAddHaarMeasure]
    {W : EuclideanSpace ℝ (Fin n) → ℝ} (hW : ContDiff ℝ 2 W) (hWc : ConvexOn ℝ Set.univ W)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∑ i, ∫ x, ‖fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2
        ∂(m.tilted (-W)) ≤
      ∫ x, weightedLaplacian W g x ^ 2 ∂(m.tilted (-W)) := by sorry
