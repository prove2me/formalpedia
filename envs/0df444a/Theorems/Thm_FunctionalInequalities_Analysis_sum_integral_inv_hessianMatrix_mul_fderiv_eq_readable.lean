-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_integral_inv_hessianMatrix_mul_fderiv_eq_readable
-- name    : FunctionalInequalities.Analysis.sum_integral_inv_hessianMatrix_mul_fderiv_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:59.197994+00:00
-- url     : https://prove2.me/theorems/6b9e4f58-2fc3-4a95-b0cc-1514a275dd70
-- title:
--   Weak Divergence Identity for the Inverse Hessian
-- statement:
--   This is the weak inverse-Hessian divergence identity, supporting the inverse-Hessian integration-by-parts route.
--
--   Let $u,F:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$. Assume:
--
--   1. $u$ is $C^1$ and has Lipschitz gradient.
--   2. $F$ is Lipschitz.
--   3. Almost everywhere,
--      $$\det(\operatorname{hessianMatrix}(u,x))=e^{F(x)}.$$
--   4. $\psi$ is Lipschitz and compactly supported.
--
--   For every $i<n$,
--
--   $$\sum_{j<n}\int H(x)^{-1}_{ij}\,D\psi(x)e_j\,dx
--   =\sum_{j<n}\int H(x)^{-1}_{ij}\,DF(x)e_j\,\psi(x)\,dx,$$
--
--   where $H(x)=\operatorname{hessianMatrix}(u,x)$ and all integrals use Lebesgue measure. The statement does not assume pointwise positive definiteness of $H$; matrix inversion is the Lean matrix inverse and the determinant identity is only almost everywhere.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_integral_inv_hessianMatrix_mul_fderiv_eq {n : ℕ}
--       {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) {G : NNReal}
--       (hG : LipschitzWith G (gradient u)) {LF : NNReal} (hF : LipschitzWith LF F)
--       (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).det = Real.exp (F x))
--       {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {Lψ : NNReal} (hψ : LipschitzWith Lψ ψ)
--       (hψc : HasCompactSupport ψ) (i : Fin n) :
--       ∑ j, ∫ x, (hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
--         ∑ j, ∫ x, (hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ j) * ψ x
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Piola`](https://prove2.me/theorems/bafaf8f6-610f-44ba-81ae-c118558a1200).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Supporting theorems: [`sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz`](https://prove2.me/theorems/9cef62de-2961-4a89-8097-dc7a3da8be64).
--
--   Previous: [`sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz`](https://prove2.me/theorems/9cef62de-2961-4a89-8097-dc7a3da8be64) · Next: [`integrable_inv_hessianMatrix_mul_of_bounded_compact`](https://prove2.me/theorems/a000c1ee-3b61-43e3-9151-d3b5dea77574).
--
--   [Source excerpt, lines 916–926](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L916-L926) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L913-L1015 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Piola`, declaration `FunctionalInequalities.Analysis.sum_integral_inv_hessianMatrix_mul_fderiv_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Piola

open FunctionalInequalities.Probability.Stein
open MeasureTheory Set Filter

theorem FunctionalInequalities.Analysis.sum_integral_inv_hessianMatrix_mul_fderiv_eq_readable {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) {LF : NNReal} (hF : LipschitzWith LF F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {Lψ : NNReal} (hψ : LipschitzWith Lψ ψ)
    (hψc : HasCompactSupport ψ) (i : Fin n) :
    ∑ j, ∫ x, (hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      ∑ j, ∫ x, (hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ j) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
