-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_inverse_hessian_row_divergence_of_weak_derivative_readable
-- name    : FunctionalInequalities.Analysis.ae_inverse_hessian_row_divergence_of_weak_derivative_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:43.83534+00:00
-- url     : https://prove2.me/theorems/e773702c-7809-4847-beb6-e121927d46e0
-- title:
--   Weak Inverse-Hessian Row Divergence
-- statement:
--   This formalizes a supporting weak inverse-Hessian identity, cited as a partial formalization of Lemma 2.4 of Letwin (arXiv:2607.24164v1).
--
--   Let $u,F:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$. Assume:
--
--   1. $u$ is $C^1$ with Lipschitz gradient, $F$ is Lipschitz, and almost everywhere $\det H=e^F$, where $H=\operatorname{hessianMatrix}(u,\cdot)$.
--   2. A tensor $T(x,k,a,b)$ is supplied together with weak directional derivatives of each entry $H(x)^{-1}_{ij}$, namely the derivative along $e_k$ is
--      $$-\bigl(H(x)^{-1}T(x,k)H(x)^{-1}\bigr)_{ij}.$$
--   3. These weak derivatives and inverse entries have the stated local $L^2$ and local $L^\infty$ (`ENNReal` exponent $\top$) membership on every compact set.
--
--   Then, for every row $b$, the vector field
--   $$x\mapsto\sum_a H(x)^{-1}_{ba}\,DF(x)e_a$$
--   belongs to $L^2$ on every compact set, and almost everywhere
--
--   $$\sum_a-\bigl(H(x)^{-1}T(x,a)H(x)^{-1}\bigr)_{ba}
--   =-\sum_a H(x)^{-1}_{ba}\,DF(x)e_a.$$
--
--   The declaration `ae_inverse_hessian_row_divergence_of_weak_derivative_readable` is an interface theorem for a fixed weak inverse-derivative object; it does not construct $T$.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--             ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
--       ∀ b : Fin n,
--         (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--           MemLp
--             (fun x => ∑ a : Fin n, (hessianMatrix u x)⁻¹ b a *
--               fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ a))
--             2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
--         ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--           (∑ a : Fin n, -(((hessianMatrix u x)⁻¹ *
--             (Matrix.of fun c d => T x a c d) * (hessianMatrix u x)⁻¹) b a)) =
--           -(∑ a : Fin n, (hessianMatrix u x)⁻¹ b a *
--             fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ a))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`sum_integral_inv_hessianMatrix_mul_fderiv_eq`](https://prove2.me/theorems/6b9e4f58-2fc3-4a95-b0cc-1514a275dd70).
--
--   Previous: [`integral_mul_generator_eq_neg_energy_of_contDiff_one`](https://prove2.me/theorems/bda30b6e-bb4c-453a-b213-90c9b1d32698).
--
--   [Source excerpt, lines 1211–1222](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L1211-L1222) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L1190-L1303 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `FunctionalInequalities.Analysis.ae_inverse_hessian_row_divergence_of_weak_derivative`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

open MeasureTheory Set
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.ae_inverse_hessian_row_divergence_of_weak_derivative_readable {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hC1 : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    {LF : NNReal} (hF : LipschitzWith LF F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hInv : ∀ k i j : Fin n,
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
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ b : Fin n,
      (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => ∑ a : Fin n, (hessianMatrix u x)⁻¹ b a *
            fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (∑ a : Fin n, -(((hessianMatrix u x)⁻¹ *
          (Matrix.of fun c d => T x a c d) * (hessianMatrix u x)⁻¹) b a)) =
        -(∑ a : Fin n, (hessianMatrix u x)⁻¹ b a *
          fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ a)) := by sorry
