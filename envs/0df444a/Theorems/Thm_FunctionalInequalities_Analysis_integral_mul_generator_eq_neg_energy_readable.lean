-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_generator_eq_neg_energy_readable
-- name    : FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:05.082746+00:00
-- url     : https://prove2.me/theorems/eb1196e2-8044-4e2b-9000-8fcc401166ec
-- title:
--   Weak Symmetry of the Inverse-Hessian Generator
-- statement:
--   This formalizes the weak form of equation (2.2) in Letwin (arXiv:2607.24164v1), with a reviewed relation to Theorem 2.5.
--
--   Let $u,V,w,\eta$ be functions on $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))$. Assume:
--
--   1. $u$ and $w$ are $C^1$;
--   2. $\nabla u$ and $\nabla w$ are Lipschitz;
--   3. $V$ is $C^1$;
--   4. $-u+V\circ\nabla u$ is Lipschitz;
--   5. almost everywhere,
--   $$\det(\operatorname{hessianMatrix}(u,x))=e^{-u(x)+V(\nabla u(x))};$$
--   6. $\eta$ is $C^2$ and compactly supported.
--
--   Then
--   $$\int \eta(x)\left(\operatorname{tr}\bigl(H_u(x)^{-1}H_w(x)\bigr)-DV(\nabla u(x))[\nabla w(x)]\right)e^{-u(x)}\,dx$$
--   $$=-\int\left(\sum_{i,j}(H_u(x)^{-1})_{ij}\,D\eta(x)[e_i]\,Dw(x)[e_j]\right)e^{-u(x)}\,dx.$$
--
--   The formula is an integration-by-parts identity for the weak inverse-Hessian generator. It uses ordinary Lebesgue integrals and an almost-everywhere determinant identity; it does not claim the main Hessian-energy estimate or any KLS bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_generator_eq_neg_energy {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
--       {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
--       (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
--       (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
--       (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
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
--   Previous: [`assemble_generator`](https://prove2.me/theorems/ecbe4dd5-bf64-4880-91be-e99fda5c9cf6) · Next: [`integral_mul_generator_eq_neg_energy'`](https://prove2.me/theorems/12ffe5ab-1e01-479f-819d-012727f89a87).
--
--   [Source excerpt, lines 770–783](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L770-L783) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L766-L795 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_readable {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ x, η x * (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x, (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
