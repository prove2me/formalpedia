-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_weak_third_derivative_symm_readable
-- name    : FunctionalInequalities.Analysis.ae_weak_third_derivative_symm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:03.862189+00:00
-- url     : https://prove2.me/theorems/236baf49-0092-428b-8c19-9934eff0cfd3
-- title:
--   Almost-Everywhere Symmetry of Weak Third Derivatives
-- statement:
--   This is a weak-coordinate symmetry statement for third derivatives.
--
--   Let $u:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$ be $C^1$ with Lipschitz gradient. Let $T(x,k,i,j)$ be such that, for every $k,i,j<n$, the function $T(\cdot,k,i,j)$ is a weak derivative along $e_k$ of the Hessian entry $H_{ij}=\operatorname{hessianMatrix}(u,\cdot)_{ij}$. Then, for almost every $x$, simultaneously for all $k,i,j$,
--
--   $$T(x,k,i,j)=T(x,i,k,j),
--   \qquad T(x,k,i,j)=T(x,k,j,i).$$
--
--   The first equality exchanges the derivative and first Hessian indices; the second expresses symmetry in the Hessian indices. The declaration `ae_weak_third_derivative_symm_readable` is an almost-everywhere identification result and does not assert that a classical third derivative exists.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_weak_third_derivative_symm {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
--       {G : NNReal} (hG : LipschitzWith G (gradient u))
--       {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
--       (hT : ∀ k i j, HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
--         (EuclideanSpace.basisFun (Fin n) ℝ k)) :
--       ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         ∀ k i j, T x k i j = T x i k j ∧ T x k i j = T x k j i
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`hasWeakDerivAlong_of_lipschitz`](https://prove2.me/theorems/b9fc0ec0-1bac-4138-9d6d-d21b20f114b9).
--
--   Next: [`norm_hessianMatrix_entry_le_of_lipschitz_gradient`](https://prove2.me/theorems/c390fe75-eaf1-41ee-934b-fddb8427fab6).
--
--   [Source excerpt, lines 160–166](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L160-L166) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L157-L281 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, declaration `FunctionalInequalities.Analysis.ae_weak_third_derivative_symm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.ae_weak_third_derivative_symm_readable {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    {G : NNReal} (hG : LipschitzWith G (gradient u))
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hT : ∀ k i j, HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
      (EuclideanSpace.basisFun (Fin n) ℝ k)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ k i j, T x k i j = T x i k j ∧ T x k i j = T x k j i := by sorry
