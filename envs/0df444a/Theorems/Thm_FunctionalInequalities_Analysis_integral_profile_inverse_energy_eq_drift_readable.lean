-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_profile_inverse_energy_eq_drift_readable
-- name    : FunctionalInequalities.Analysis.integral_profile_inverse_energy_eq_drift_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:54.242986+00:00
-- url     : https://prove2.me/theorems/37eca32c-ff0d-4e58-b29e-ac1ed53cd43e
-- title:
--   Profile Inverse-Energy Drift Identity
-- statement:
--   This is an identity for a compactly supported profile of a Monge–Ampère potential.
--
--   Let $u,V:\mathbb R^n\to\mathbb R$ satisfy the stated $C^1$, Lipschitz-gradient, Lipschitz-exponent, and a.e. Monge–Ampère determinant hypotheses. Let $\zeta:\mathbb R\to\mathbb R$ be $C^1$ and assume $x\mapsto\zeta(u(x))$ has compact support. Then the weighted inverse-Hessian energy density
--   $$
--   \zeta'(u)
--   \sum_{i,j}(\nabla^2u)^{-1}_{ij}\,\partial_i u\,\partial_j u\,e^{-u}
--   $$
--   is integrable, and
--
--   $$
--   \int -\zeta'(u)\sum_{i,j}(\nabla^2u)^{-1}_{ij}\partial_i u\partial_j u\,e^{-u}
--   =\int \zeta(u)\left(n-\nabla V(\nabla u)\cdot\nabla u\right)e^{-u}.
--   $$
--
--   This result is a profile specialization of the weighted generator identity used in height-cutoff estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem integral_profile_inverse_energy_eq_drift {n : ℕ}
--       {u V : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G LF : NNReal}
--       (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
--       (hV : ContDiff ℝ 1 V)
--       (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
--       (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
--       (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport (fun x => ζ (u x))) :
--       Integrable (fun x =>
--         (deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
--           fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
--           fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x))
--         (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--       (∫ x, -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
--           fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
--           fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x)
--         ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--       ∫ x, ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) *
--         Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff`](https://prove2.me/theorems/43fb64bd-b52a-486a-aa88-c80fa40c379d).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Supporting theorems: [`integrable_inv_hessianMatrix_mul_of_bounded_compact`](https://prove2.me/theorems/a000c1ee-3b61-43e3-9151-d3b5dea77574), [`integral_mul_generator_eq_neg_energy_of_contDiff_one`](https://prove2.me/theorems/bda30b6e-bb4c-453a-b213-90c9b1d32698).
--
--   Next: [`ae_hessianMatrix_comp_profile`](https://prove2.me/theorems/a20a6531-08f1-4bad-8e32-e9848449abfb).
--
--   [Source excerpt, lines 65–83](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L65-L83) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L65-L137 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff.0.FunctionalInequalities.Analysis.integral_profile_inverse_energy_eq_drift`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_WeakCutoff

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.integral_profile_inverse_energy_eq_drift_readable {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport (fun x => ζ (u x))) :
    Integrable (fun x =>
      (deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    ∫ x, ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) *
      Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
