-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_generator_eq_neg_energy_of_contDiff_one_readable
-- name    : FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_of_contDiff_one_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:52.625629+00:00
-- url     : https://prove2.me/theorems/bda30b6e-bb4c-453a-b213-90c9b1d32698
-- title:
--   Weighted Weak Inverse-Hessian Generator Identity
-- statement:
--   This is a weak inverse-Hessian integration-by-parts identity associated with equation (2.2) of Letwin (arXiv:2607.24164v1), and supports Lemma A.4.
--
--   Let $u,V,w,\eta:\mathbb R^n\to\mathbb R$ be $C^1$, with $u$ having Lipschitz gradient, $V$ having the stated $C^1$ regularity, and $w$ having Lipschitz gradient. Assume $-u+V\circ\nabla u$ is Lipschitz and
--   $$
--   \det\nabla^2u=\exp(-u+V(\nabla u))
--   $$
--   a.e. Assume that $\eta$ is compactly supported. Then
--
--   $$
--   \int \eta(x)\left(\operatorname{tr}\bigl((\nabla^2u(x))^{-1}\nabla^2w(x)\bigr)
--   -\nabla V(\nabla u(x))\cdot\nabla w(x)\right)e^{-u(x)}\,dx
--   $$
--   $$
--   =-\int\left(\sum_{i,j}(\nabla^2u(x))^{-1}_{ij}\,\partial_i\eta(x)\,\partial_jw(x)\right)e^{-u(x)}\,dx.
--   $$
--
--   The statement uses only $C^1$ regularity for the displayed functions and supplies the weighted generator–energy identity for compact multipliers.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_generator_eq_neg_energy_of_contDiff_one {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
--       {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
--       (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
--       (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
--       (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
--       ∫ x, η x * (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
--           fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x)
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
--         -∫ x, (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
--             fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
--             fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Supporting theorems: [`integrable_inv_hessianMatrix_mul_of_bounded_compact`](https://prove2.me/theorems/a000c1ee-3b61-43e3-9151-d3b5dea77574), [`exists_lipschitzWith_smul_of_locallyLipschitz`](https://prove2.me/theorems/a69c5efc-cc10-4d88-8cc4-a8588fa667cb), [`assemble_generator`](https://prove2.me/theorems/ecbe4dd5-bf64-4880-91be-e99fda5c9cf6).
--
--   Previous: [`hasWeakDerivAlong_inverse_hessian_of_logdet`](https://prove2.me/theorems/6e913d0c-8e93-456f-8534-533355d49266) · Next: [`ae_inverse_hessian_row_divergence_of_weak_derivative`](https://prove2.me/theorems/e773702c-7809-4847-beb6-e121927d46e0).
--
--   [Source excerpt, lines 1152–1165](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L1152-L1165) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L1150-L1177 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_of_contDiff_one`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

open MeasureTheory
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_of_contDiff_one_readable {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ x, η x * (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x, (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
