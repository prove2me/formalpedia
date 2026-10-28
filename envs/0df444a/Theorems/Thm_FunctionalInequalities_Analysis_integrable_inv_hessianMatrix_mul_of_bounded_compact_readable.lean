-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integrable_inv_hessianMatrix_mul_of_bounded_compact_readable
-- name    : FunctionalInequalities.Analysis.integrable_inv_hessianMatrix_mul_of_bounded_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:35.759626+00:00
-- url     : https://prove2.me/theorems/a000c1ee-3b61-43e3-9151-d3b5dea77574
-- title:
--   Integrability of Compact Multipliers Against Inverse Hessian Entries
-- statement:
--   This is an integrability component related to Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $u,F,f:\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))\to\mathbb R$, let $G\in\mathbb R_{\ge0}$, and assume:
--
--   1. $\nabla u$ is Lipschitz with constant $G$;
--   2. $F$ is continuous;
--   3. almost everywhere,
--   $$\det(\operatorname{hessianMatrix}(u,x))=e^{F(x)};$$
--   4. $f$ is measurable and compactly supported;
--   5. there is $C\in\mathbb R$ with $\|f(x)\|\le C$ for every $x$.
--
--   Then for every $i,j$,
--   $$x\mapsto \bigl(\operatorname{hessianMatrix}(u,x)^{-1}\bigr)_{ij}f(x)$$
--   is integrable with respect to volume.
--
--   The determinant identity is only assumed almost everywhere, and the conclusion concerns individual inverse-matrix entries rather than a matrix-valued integral.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_inv_hessianMatrix_mul_of_bounded_compact {n : ℕ}
--       {u F f : EuclideanSpace ℝ (Fin n) → ℝ}
--       {G : NNReal} (hG : LipschitzWith G (gradient u)) (hF : Continuous F)
--       (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).det = Real.exp (F x))
--       (hf : Measurable f) (hfc : HasCompactSupport f)
--       {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (i j : Fin n) :
--       Integrable (fun x => (hessianMatrix u x)⁻¹ i j * f x)
--         (volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Piola`](https://prove2.me/theorems/bafaf8f6-610f-44ba-81ae-c118558a1200).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Previous: [`sum_integral_inv_hessianMatrix_mul_fderiv_eq`](https://prove2.me/theorems/6b9e4f58-2fc3-4a95-b0cc-1514a275dd70) · Next: [`exists_weak_hessian_adjugate_derivative`](https://prove2.me/theorems/67ea3932-bb12-489c-b021-f170ae02b2db).
--
--   [Source excerpt, lines 1019–1027](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L1019-L1027) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L1017-L1061 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Piola`, declaration `FunctionalInequalities.Analysis.integrable_inv_hessianMatrix_mul_of_bounded_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Piola

open FunctionalInequalities.Probability.Stein
open MeasureTheory Set Filter

theorem FunctionalInequalities.Analysis.integrable_inv_hessianMatrix_mul_of_bounded_compact_readable {n : ℕ}
    {u F f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : NNReal} (hG : LipschitzWith G (gradient u)) (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (hf : Measurable f) (hfc : HasCompactSupport f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (i j : Fin n) :
    Integrable (fun x => (hessianMatrix u x)⁻¹ i j * f x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
