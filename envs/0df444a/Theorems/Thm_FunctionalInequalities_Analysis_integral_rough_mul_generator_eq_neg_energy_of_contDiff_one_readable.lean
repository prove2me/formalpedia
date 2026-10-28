-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_rough_mul_generator_eq_neg_energy_of_contDiff_one_readable
-- name    : FunctionalInequalities.Analysis.integral_rough_mul_generator_eq_neg_energy_of_contDiff_one_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:05.603831+00:00
-- url     : https://prove2.me/theorems/f2c8c826-3a52-44a7-a05b-5384299f9b32
-- title:
--   Rough Inverse-Hessian Generator–Energy Identity
-- statement:
--   This is a rough weak-test version of the inverse-Hessian generator identity associated with Lemma A.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $u,V,\chi:\mathbb R^n\to\mathbb R$ be $C^1$, with $u$ having Lipschitz gradient and $\chi$ having Lipschitz gradient and compact support. Assume $-u+V\circ\nabla u$ is Lipschitz and
--   $$
--   \det\nabla^2u=\exp(-u+V(\nabla u))
--   $$
--   a.e. Assume compact-local `ENNReal` $L^\infty$ bounds for the entries of $(\nabla^2u)^{-1}$ and integrability of
--   $$
--   \left(\operatorname{tr}((\nabla^2u)^{-1}\nabla^2\chi)
--   -\nabla V(\nabla u)\cdot\nabla\chi\right)e^{-u}.
--   $$
--   Let $\eta$ be locally integrable and bounded by $C$, and let $a_i$ be its weak coordinate derivatives, compact-locally in $L^2$.
--
--   Then both displayed pairings are integrable and
--
--   $$
--   \int \eta(x)\left(\operatorname{tr}((\nabla^2u(x))^{-1}\nabla^2\chi(x))
--   -\nabla V(\nabla u(x))\cdot\nabla\chi(x)\right)e^{-u(x)}\,dx
--   $$
--   $$
--   =-\int\left(\sum_{i,j}(\nabla^2u(x))^{-1}_{ij}a_i(x)\partial_j\chi(x)\right)e^{-u(x)}\,dx.
--   $$
--
--   This is the rough testing interface used for bounded weak functions against height cutoffs.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--         (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
--           fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x))
--         (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--       Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
--         a i x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
--         (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--       (∫ x, η x * (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
--         fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x)
--         ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--       -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
--         a i x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
--         ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff`](https://prove2.me/theorems/43fb64bd-b52a-486a-aa88-c80fa40c379d).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test`](https://prove2.me/theorems/68f53a73-98d0-4677-9ebd-c4a0016296fd), [`integral_mul_generator_eq_neg_energy_of_contDiff_one`](https://prove2.me/theorems/bda30b6e-bb4c-453a-b213-90c9b1d32698).
--
--   Previous: [`exists_scaled_weak_inverse_hessian_cutoffs`](https://prove2.me/theorems/668b9b15-6105-43f9-a200-099e2fd7f3b7).
--
--   [Source excerpt, lines 939–950](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L939-L950) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L912-L1009 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff`, declaration `FunctionalInequalities.Analysis.integral_rough_mul_generator_eq_neg_energy_of_contDiff_one`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_WeakCutoff

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.integral_rough_mul_generator_eq_neg_energy_of_contDiff_one_readable {n : ℕ}
    {u V χ η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) {LF : NNReal}
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hχ : ContDiff ℝ 1 χ) {Gχ : NNReal} (hGχ : LipschitzWith Gχ (gradient χ))
    (hχc : HasCompactSupport χ)
    (hInv : ∀ i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hForce : Integrable (fun x =>
      (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {C : ℝ} (hbound : ∀ x, ‖η x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    Integrable (fun x => η x *
      (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
      a i x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, η x * (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
      fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
      a i x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
