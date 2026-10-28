-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_inverse_hessian_of_logdet_readable
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_inverse_hessian_of_logdet_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:37.608883+00:00
-- url     : https://prove2.me/theorems/6e913d0c-8e93-456f-8534-533355d49266
-- title:
--   Weak Derivative of the Inverse Hessian
-- statement:
--   Let $u,F:\mathbb{R}^n\to\mathbb{R}$, let $\nabla u$ be Lipschitz, let $F$ be Lipschitz, and assume that almost everywhere the Hessian $H_u$ is positive definite and
--
--   $$
--   \log\det H_u=F.
--   $$
--
--   Suppose a tensor $T$ gives locally $L^2$ weak directional derivatives of the entries of $H_u$. Then, for every coordinate direction $e_k$ and indices $i,j$, the inverse Hessian has weak derivative
--
--   $$
--   \partial_k(H_u^{-1})_{ij}
--   =-\bigl(H_u^{-1}T_kH_u^{-1}\bigr)_{ij},
--   $$
--
--   and this derivative is locally in $L^2$ on compact sets. The inverse-Hessian entries themselves are locally in $L^{\infty}$ on compact sets. This is a weak calculus statement and does not assume $C^2$ regularity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasWeakDerivAlong_inverse_hessian_of_logdet {n : ℕ}
--       {u F : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
--       {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
--       (hG : LipschitzWith G (gradient u)) (hF : LipschitzWith LF F)
--       (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).PosDef ∧ Real.log (hessianMatrix u x).det = F x)
--       (hT : ∀ k i j : Fin n,
--         HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
--           (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
--         ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--           MemLp (fun x => T x k i j) 2
--             ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
--       ∀ k i j : Fin n,
--         HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
--           (fun x => -(((hessianMatrix u x)⁻¹ *
--             (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
--           (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
--         (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--           MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
--             (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
--             ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
--         ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--           MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
--             ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Selected supporting theorems: [`HasWeakDerivAlong.congr_ae`](https://prove2.me/theorems/feacd1e3-2d93-4444-8c84-fe52a0849220), [`HasWeakDerivAlong.mul_of_locally_bounded`](https://prove2.me/theorems/1133273b-c737-4c38-bf2a-2953cd23a941), [`ae_weak_matrix_inverse_derivative`](https://prove2.me/theorems/d6fe03d3-18d4-4ee9-8216-cfc3ec407a97), [`exists_weak_hessian_adjugate_derivative`](https://prove2.me/theorems/67ea3932-bb12-489c-b021-f170ae02b2db), [`hasWeakDerivAlong_exp_neg_of_lipschitz`](https://prove2.me/theorems/bacd1f1f-068d-4e42-88a3-d15ac6d6ee33).
--
--   Previous: [`integrable_weak_generator_densities`](https://prove2.me/theorems/24449bc6-0de3-4efc-93a6-7a73a3bded73) · Next: [`integral_mul_generator_eq_neg_energy_of_contDiff_one`](https://prove2.me/theorems/bda30b6e-bb4c-453a-b213-90c9b1d32698).
--
--   [Source excerpt, lines 1053–1076](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L1053-L1076) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L1051-L1138 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_inverse_hessian_of_logdet`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

open MeasureTheory Set Filter Metric Matrix
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_inverse_hessian_of_logdet_readable {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hG : LipschitzWith G (gradient u)) (hF : LipschitzWith LF F)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧ Real.log (hessianMatrix u x).det = F x)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
        (fun x => -(((hessianMatrix u x)⁻¹ *
          (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
          (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by sorry
