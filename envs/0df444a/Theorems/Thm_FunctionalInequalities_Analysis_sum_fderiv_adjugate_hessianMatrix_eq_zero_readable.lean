-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_fderiv_adjugate_hessianMatrix_eq_zero_readable
-- name    : FunctionalInequalities.Analysis.sum_fderiv_adjugate_hessianMatrix_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:30.158767+00:00
-- url     : https://prove2.me/theorems/d9abe498-7a4a-408f-882a-341a822f2253
-- title:
--   Piola Identity for Smooth Hessian Adjugates
-- statement:
--   This is the smooth Piola identity for Hessian adjugates.
--
--   Let $n\in\mathbb N$, let $u:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$ be $C^3$, and let $x$ be a point and $i<n$ a row index. If $H(y)=\operatorname{hessianMatrix}(u,y)$, then
--
--   $$\sum_{j<n}D\bigl[y\mapsto \operatorname{adj}(H(y))_{ij}\bigr](x)e_j=0,$$
--
--   where $e_j$ is the standard coordinate vector. The declaration `sum_fderiv_adjugate_hessianMatrix_eq_zero_readable` states that each row of the adjugate Hessian is divergence-free. It is the smooth input for later weak Piola identities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_fderiv_adjugate_hessianMatrix_eq_zero {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : ContDiff ℝ 3 u) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
--       ∑ j, fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x
--         (EuclideanSpace.basisFun (Fin n) ℝ j) = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Piola`](https://prove2.me/theorems/bafaf8f6-610f-44ba-81ae-c118558a1200).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Supporting theorems: [`fderiv_det_updateRow`](https://prove2.me/theorems/67074ad1-cbd5-49f9-85c5-5090bdb537d6).
--
--   Previous: [`fderiv_det_updateRow`](https://prove2.me/theorems/67074ad1-cbd5-49f9-85c5-5090bdb537d6) · Next: [`sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz`](https://prove2.me/theorems/9cef62de-2961-4a89-8097-dc7a3da8be64).
--
--   [Source excerpt, lines 135–138](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L135-L138) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L131-L270 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Piola`, declaration `FunctionalInequalities.Analysis.sum_fderiv_adjugate_hessianMatrix_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Piola

open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.sum_fderiv_adjugate_hessianMatrix_eq_zero_readable {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 3 u) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ∑ j, fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x
      (EuclideanSpace.basisFun (Fin n) ℝ j) = 0 := by sorry
