-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz_readable
-- name    : FunctionalInequalities.Analysis.sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:43.161551+00:00
-- url     : https://prove2.me/theorems/9cef62de-2961-4a89-8097-dc7a3da8be64
-- title:
--   Weak Piola Identity with Lipschitz Test Functions
-- statement:
--   This is the weak Piola identity for Lipschitz test functions.
--
--   Let $n\in\mathbb N$, let $u:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$ be $C^1$ with Lipschitz gradient, and let $\psi$ be Lipschitz with compact support. For every row index $i<n$,
--
--   $$\sum_{j<n}\int \operatorname{adj}(H(x))_{ij}\,D\psi(x)e_j\,dx=0,$$
--
--   where $H(x)=\operatorname{hessianMatrix}(u,x)$ and the integral is with respect to Lebesgue measure. The declaration `sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz_readable` is a weak, integrated version of the smooth Piola identity. No positivity or invertibility of the Hessian is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz {n : ℕ}
--       {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) {G : NNReal}
--       (hG : LipschitzWith G (gradient u)) {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {Lψ : NNReal}
--       (hψ : LipschitzWith Lψ ψ) (hψc : HasCompactSupport ψ) (i : Fin n) :
--       ∑ j, ∫ x, (hessianMatrix u x).adjugate i j * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)
--         ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Piola`](https://prove2.me/theorems/bafaf8f6-610f-44ba-81ae-c118558a1200).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Supporting theorems: [`exists_contDiff_approx_of_lipschitz_gradient`](https://prove2.me/theorems/58f49398-895c-40bc-ab6b-62bb53052379), [`sum_fderiv_adjugate_hessianMatrix_eq_zero`](https://prove2.me/theorems/d9abe498-7a4a-408f-882a-341a822f2253).
--
--   Previous: [`sum_fderiv_adjugate_hessianMatrix_eq_zero`](https://prove2.me/theorems/d9abe498-7a4a-408f-882a-341a822f2253) · Next: [`sum_integral_inv_hessianMatrix_mul_fderiv_eq`](https://prove2.me/theorems/6b9e4f58-2fc3-4a95-b0cc-1514a275dd70).
--
--   [Source excerpt, lines 822–827](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L822-L827) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L819-L846 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Piola`, declaration `FunctionalInequalities.Analysis.sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Piola

open FunctionalInequalities.Probability.Stein
open MeasureTheory Set Filter
variable {E : Type*}

theorem FunctionalInequalities.Analysis.sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz_readable {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {Lψ : NNReal}
    (hψ : LipschitzWith Lψ ψ) (hψc : HasCompactSupport ψ) (i : Fin n) :
    ∑ j, ∫ x, (hessianMatrix u x).adjugate i j * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 0 := by sorry
