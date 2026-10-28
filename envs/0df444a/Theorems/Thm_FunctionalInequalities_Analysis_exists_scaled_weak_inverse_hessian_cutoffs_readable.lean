-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_scaled_weak_inverse_hessian_cutoffs_readable
-- name    : FunctionalInequalities.Analysis.exists_scaled_weak_inverse_hessian_cutoffs_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:48.355761+00:00
-- url     : https://prove2.me/theorems/668b9b15-6105-43f9-a200-099e2fd7f3b7
-- title:
--   Scaled Weak Inverse-Hessian Height Cutoffs
-- statement:
--   This is the weak $C^1$ cutoff construction associated with Lemma A.4 of Letwin (arXiv:2607.24164v1), and is used in the proof architecture surrounding Theorem 2.5.
--
--   Let $u,V:\mathbb R^n\to\mathbb R$ satisfy the stated $C^1$ regularity, Lipschitzness of $u$ and $\nabla u$, Lipschitzness of $-u+V\circ\nabla u$, the a.e. Monge–Ampère identity, and a.e. positive definiteness of $\nabla^2u$. Assume $u$ is convex and normalized by $\int e^{-u}=1$.
--
--   Then there exist $c,C\in\mathbb R$ with $C\ge0$ and $u(x)-c\ge1$ for every $x$ such that, writing
--   $$
--   \chi_R(x)=\operatorname{smoothTransition}\left(2-\frac{u(x)-c}{R}\right),
--   $$
--   and
--   $$
--   L\chi_R=\operatorname{tr}\bigl((\nabla^2u)^{-1}\nabla^2\chi_R\bigr)-\nabla V(\nabla u)\cdot\nabla\chi_R,
--   $$
--   for every $R\ge1$, $\chi_R$ is $C^1$, compactly supported, has a Lipschitz gradient, and satisfies $0\le\chi_R\le1$. For each $x$, $R\mapsto\chi_R(x)$ is monotone on $[1,\infty)$ and tends to $1$. Moreover, $L\chi_R$ is integrable with respect to the tilted measure $e^{-u}dx$, and
--
--   $$
--   \int |L\chi_R|\,d(e^{-u}dx)\le\frac{C}{R}.
--   $$
--
--   The same integral tends to $0$ as $R\to\infty$. This is an existence statement for a cutoff family, not an estimate for arbitrary cutoffs.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_scaled_weak_inverse_hessian_cutoffs {n : ℕ}
--       {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
--       (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
--       (hV : ContDiff ℝ 1 V)
--       (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
--       (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
--       (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u x).PosDef)
--       (hconv : ConvexOn ℝ univ u)
--       (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1) :
--       ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
--         let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
--         let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
--           fderiv ℝ V (gradient u x) (gradient (χ R) x)
--         (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
--           (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
--           ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
--         (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
--         (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
--         (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
--           ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
--         (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
--           ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
--         Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
--           ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff`](https://prove2.me/theorems/43fb64bd-b52a-486a-aa88-c80fa40c379d).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Selected supporting theorems: [`deriv_comp_sub_div_and_deriv_deriv`](https://prove2.me/theorems/41078cd2-f599-4095-aec6-d7ad2870689d), [`exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg`](https://prove2.me/theorems/d27371ec-adba-4761-8a3a-e229679243d0), [`inv_mul_intervalIntegral_div_three_cutoff`](https://prove2.me/theorems/84c111d5-1c7e-41d4-975d-61430e96ccc6), [`monotoneOn_and_tendsto_smoothTransition_two_sub_div`](https://prove2.me/theorems/07c7bff6-a883-4a34-a1d3-2095c97849b8), [`smoothTransition_two_sub_cutoff`](https://prove2.me/theorems/107a6021-a617-4338-a167-9789f56e48be).
--
--   Previous: [`exists_C1_height_generator_defect_bound`](https://prove2.me/theorems/e4f716ac-97c9-41de-a9ed-1a6f2468efbb) · Next: [`integral_rough_mul_generator_eq_neg_energy_of_contDiff_one`](https://prove2.me/theorems/f2c8c826-3a52-44a7-a05b-5384299f9b32).
--
--   [Source excerpt, lines 773–797](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L773-L797) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L772-L838 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff`, declaration `FunctionalInequalities.Analysis.exists_scaled_weak_inverse_hessian_cutoffs`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_WeakCutoff

open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace

theorem FunctionalInequalities.Analysis.exists_scaled_weak_inverse_hessian_cutoffs_readable {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u x).PosDef)
    (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1) :
    ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ V (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) := by sorry
