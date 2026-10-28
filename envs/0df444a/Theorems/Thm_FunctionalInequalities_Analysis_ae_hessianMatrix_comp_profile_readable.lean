-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_hessianMatrix_comp_profile_readable
-- name    : FunctionalInequalities.Analysis.ae_hessianMatrix_comp_profile_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:53.289807+00:00
-- url     : https://prove2.me/theorems/a20a6531-08f1-4bad-8e32-e9848449abfb
-- title:
--   Almost-Everywhere Hessian Chain Rule for a Profile
-- statement:
--   This is an almost-everywhere chain rule for Hessians.
--
--   Let $u:\mathbb R^n\to\mathbb R$ be $C^1$ with Lipschitz gradient, and let $\zeta:\mathbb R\to\mathbb R$ be $C^2$. Then, for almost every $x$ and all $i,j\in\operatorname{Fin} n$,
--
--   $$
--   \partial_{ij}^2(\zeta\circ u)(x)
--   =\zeta'(u(x))\,\partial_{ij}^2u(x)
--   +\zeta''(u(x))\,\partial_i u(x)\,\partial_j u(x).
--   $$
--
--   In Lean, the Hessian is the coordinate matrix `hessianMatrix`, and the first derivatives are expressed using `fderiv` on the Euclidean basis. This identity supports the inverse-Hessian cutoff calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem ae_hessianMatrix_comp_profile {n : ℕ}
--       {u : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G : NNReal}
--       (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
--       (hζ : ContDiff ℝ 2 ζ) :
--       ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j : Fin n,
--         hessianMatrix (fun y => ζ (u y)) x i j =
--           deriv ζ (u x) * hessianMatrix u x i j +
--             deriv (deriv ζ) (u x) *
--               fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
--               fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff`](https://prove2.me/theorems/43fb64bd-b52a-486a-aa88-c80fa40c379d).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Previous: [`integral_profile_inverse_energy_eq_drift`](https://prove2.me/theorems/37eca32c-ff0d-4e58-b29e-ac1ed53cd43e) · Next: [`exists_C1_height_generator_defect_bound`](https://prove2.me/theorems/e4f716ac-97c9-41de-a9ed-1a6f2468efbb).
--
--   [Source excerpt, lines 373–382](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L373-L382) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L373-L426 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff.0.FunctionalInequalities.Analysis.ae_hessianMatrix_comp_profile`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_WeakCutoff

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.ae_hessianMatrix_comp_profile_readable {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hζ : ContDiff ℝ 2 ζ) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j : Fin n,
      hessianMatrix (fun y => ζ (u y)) x i j =
        deriv ζ (u x) * hessianMatrix u x i j +
          deriv (deriv ζ) (u x) *
            fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
            fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) := by sorry
