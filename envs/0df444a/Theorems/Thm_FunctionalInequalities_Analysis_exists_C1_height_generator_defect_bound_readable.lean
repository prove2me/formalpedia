-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_C1_height_generator_defect_bound_readable
-- name    : FunctionalInequalities.Analysis.exists_C1_height_generator_defect_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:52.995473+00:00
-- url     : https://prove2.me/theorems/e4f716ac-97c9-41de-a9ed-1a6f2468efbb
-- title:
--   Height-Cutoff Generator Defect Bound
-- statement:
--   This is a quantitative cutoff estimate supporting the weak inverse-Hessian height cutoffs.
--
--   Let $u,V:\mathbb R^n\to\mathbb R$ satisfy the stated $C^1$ and Lipschitz assumptions, the Lipschitz Monge–Ampère exponent, the a.e. determinant identity, a.e. positive definiteness of $\nabla^2u$, and the normalization
--   $$
--   \int e^{-u}=1.
--   $$
--   Assume every sublevel set $\{x:u(x)\le t\}$ is compact. Let $D\ge0$ satisfy
--   $$
--   \left|n-\nabla V(\nabla u(x))\cdot\nabla u(x)\right|\le D
--   $$
--   for every $x$, and fix $c\in\mathbb R$.
--
--   Then there exists $C\ge0$ such that for every $R\ge1$, with
--   $$
--   \chi_R(x)=\operatorname{smoothTransition}\left(2-\frac{u(x)-c}{R}\right),
--   $$
--   and
--   $$
--   L\chi_R=\operatorname{tr}\bigl((\nabla^2u)^{-1}\nabla^2\chi_R\bigr)
--   -\nabla V(\nabla u)\cdot\nabla\chi_R,
--   $$
--   $L\chi_R$ multiplied by $e^{-u}$ is integrable and
--
--   $$
--   \int |L\chi_R|e^{-u}\le \frac{C}{R}.
--   $$
--
--   This estimate supplies the decay rate for the generator defect.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem exists_C1_height_generator_defect_bound {n : ℕ}
--       {u V : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
--       (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
--       (hV : ContDiff ℝ 1 V)
--       (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
--       (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
--       (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).PosDef)
--       (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
--       (hsub : ∀ t : ℝ, IsCompact {x | u x ≤ t})
--       {D : ℝ} (hD : 0 ≤ D)
--       (hdrift : ∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D)
--       (c : ℝ) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
--         let χ := fun x => Real.smoothTransition (2 - (u x - c) / R)
--         let Lχ := fun x => ((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
--           fderiv ℝ V (gradient u x) (gradient χ x)
--         Integrable (fun x => Lχ x * Real.exp (-u x))
--           (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--         (∫ x, |Lχ x| * Real.exp (-u x)
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ C / R
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff`](https://prove2.me/theorems/43fb64bd-b52a-486a-aa88-c80fa40c379d).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Selected supporting theorems: [`deriv_comp_sub_div_and_deriv_deriv`](https://prove2.me/theorems/41078cd2-f599-4095-aec6-d7ad2870689d), [`exists_majorant_abs_deriv_deriv_smoothTransition_two_sub`](https://prove2.me/theorems/75594fe5-03f9-45fd-97be-284edaa2d948), [`inv_mul_intervalIntegral_div_three_cutoff`](https://prove2.me/theorems/84c111d5-1c7e-41d4-975d-61430e96ccc6), [`smoothTransition_two_sub_cutoff`](https://prove2.me/theorems/107a6021-a617-4338-a167-9789f56e48be), [`ae_hessianMatrix_comp_profile`](https://prove2.me/theorems/a20a6531-08f1-4bad-8e32-e9848449abfb).
--
--   Previous: [`ae_hessianMatrix_comp_profile`](https://prove2.me/theorems/a20a6531-08f1-4bad-8e32-e9848449abfb) · Next: [`exists_scaled_weak_inverse_hessian_cutoffs`](https://prove2.me/theorems/668b9b15-6105-43f9-a200-099e2fd7f3b7).
--
--   [Source excerpt, lines 614–635](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L614-L635) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L614-L769 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff.0.FunctionalInequalities.Analysis.exists_C1_height_generator_defect_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_WeakCutoff

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.exists_C1_height_generator_defect_bound_readable {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hsub : ∀ t : ℝ, IsCompact {x | u x ≤ t})
    {D : ℝ} (hD : 0 ≤ D)
    (hdrift : ∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D)
    (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      let χ := fun x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun x => ((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)
      Integrable (fun x => Lχ x * Real.exp (-u x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, |Lχ x| * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ C / R := by sorry
