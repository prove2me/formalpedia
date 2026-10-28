-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_weak_third_derivative_readable
-- name    : FunctionalInequalities.Analysis.exists_weak_third_derivative_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:49.005365+00:00
-- url     : https://prove2.me/theorems/01da6e3a-40eb-47f5-afa9-095719a6d051
-- title:
--   Weak Third Derivatives of the Hessian
-- statement:
--   This formalizes a weak local regularity statement associated with Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   For $u,V:\mathbb{R}^n\to\mathbb{R}$, assume $u$ is $C^1$ and convex, $\nabla u$ is globally Lipschitz, $V$ is $C^1$ and convex, and $-u+V\circ\nabla u$ is Lipschitz. Assume also that $K>0$, that almost everywhere
--
--   $$
--   H_u\succ0,
--   \qquad \log\det H_u=-u+V(\nabla u),
--   \qquad KI-H_u\succeq0,
--   $$
--
--   and that for some $D\in\mathbb{R}$,
--
--   $$
--    u(x+h)+u(x-h)-2u(x)\le D\|h\|^2
--   $$
--
--   for all $x,h$. Then there exists a tensor $T(x,k,i,j)$ such that every Hessian entry $H_u(x)_{ij}$ has weak derivative $T(x,k,i,j)$ in the coordinate direction $e_k$, and each such derivative belongs locally to $L^2$ on every compact set. This is a technical weak-derivative conclusion and does not assert classical third derivatives.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_weak_third_derivative {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
--       (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
--       {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ} (hK : 0 < K)
--       (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).PosDef ∧
--         Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
--         (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
--       {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
--       ∃ T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ, ∀ k i j,
--         HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
--             (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
--           ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--             MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/HessianRegularity`](https://prove2.me/theorems/3de085c3-1487-424e-b91c-badb9e79b607).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`exists_hasWeakDerivAlong_of_forall_cutoff`](https://prove2.me/theorems/db832ddc-e6e0-4365-ace7-102695429d13), [`exists_hasWeakDerivAlong_of_sq_difference_le`](https://prove2.me/theorems/75fca118-0385-4fa0-a865-9c9b02ff0dda), [`exists_hessian_cutoff_sq_difference_bound`](https://prove2.me/theorems/54515687-f5b2-40e0-b262-9c29f518ff9c), [`memLp_cutoff_mul_hessianMatrix_entry`](https://prove2.me/theorems/a87ed401-510c-4f6e-8e89-854801032ee1), [`norm_hessianMatrix_entry_le_of_lipschitz_gradient`](https://prove2.me/theorems/c390fe75-eaf1-41ee-934b-fddb8427fab6).
--
--   [Source excerpt, lines 18–31](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/HessianRegularity.lean#L18-L31) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/HessianRegularity.lean#L15-L51 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.HessianRegularity`, declaration `FunctionalInequalities.Analysis.exists_weak_third_derivative`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_HessianRegularity

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.exists_weak_third_derivative_readable {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    ∃ T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ, ∀ k i j,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by sorry
