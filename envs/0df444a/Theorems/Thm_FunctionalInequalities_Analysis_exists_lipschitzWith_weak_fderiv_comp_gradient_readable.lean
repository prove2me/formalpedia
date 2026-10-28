-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_lipschitzWith_weak_fderiv_comp_gradient_readable
-- name    : FunctionalInequalities.Analysis.exists_lipschitzWith_weak_fderiv_comp_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:36.977998+00:00
-- url     : https://prove2.me/theorems/2b6867a4-8c8c-4420-8df5-b75bc2ce4bd7
-- title:
--   Weak Derivative of a Composed Coordinate Derivative
-- statement:
--   This is a supporting weak-Hessian statement for the second evolution identity of Letwin (arXiv:2607.24164v1), equation (2.6).
--
--   Let $u,W:\mathbb R^n\to\mathbb R$. Assume $u\in C^1$, $u$ is globally Lipschitz, $\nabla u$ is globally Lipschitz, and $W\in C^2$. For each $a\in\mathrm{Fin}\ n$, there exists $C\in[0,\infty)$ such that $x\mapsto DW(\nabla u(x))[e_a]$ is $C$-Lipschitz. For every $j$, it has a weak derivative along $e_j$ given by
--
--   $$\sum_b H_u(x)_{jb}\,H_W(\nabla u(x))_{ba}.$$
--
--   This derivative belongs to $L^2$ on every compact set. No global $L^2$ estimate or inverse-Hessian bound is asserted.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_lipschitzWith_weak_fderiv_comp_gradient {n : ℕ}
--       {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
--       (hu : ContDiff ℝ 1 u) (hULip : LipschitzWith L u)
--       (hGradLip : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
--       (a : Fin n) :
--       ∃ C : NNReal,
--         LipschitzWith C (fun x => fderiv ℝ W (gradient u x)
--           (EuclideanSpace.basisFun (Fin n) ℝ a)) ∧
--         ∀ j : Fin n,
--           HasWeakDerivAlong
--             (fun x => fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
--             (fun x => ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
--             (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
--           ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--             MemLp
--               (fun x => ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
--               2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution`](https://prove2.me/theorems/d20d941d-a690-4ebe-9a63-a346adf8dd16).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`HasWeakDerivAlong.congr_ae`](https://prove2.me/theorems/feacd1e3-2d93-4444-8c84-fe52a0849220), [`ae_fderiv_mongeAmpere_exponent`](https://prove2.me/theorems/71049741-6710-4957-9e2a-2a505bfab529), [`exists_lipschitzWith_neg_add_comp_gradient`](https://prove2.me/theorems/e0b4ed2f-da69-4e68-a1df-7fa0bdfaa735), [`hasWeakDerivAlong_of_lipschitz`](https://prove2.me/theorems/b9fc0ec0-1bac-4138-9d6d-d21b20f114b9).
--
--   Next: [`hasWeakDerivAlong_mongeAmpere_first_rhs`](https://prove2.me/theorems/55f12f10-6c36-4776-96b3-387313b3b590).
--
--   [Source excerpt, lines 86–102](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L86-L102) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L83-L249 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, declaration `FunctionalInequalities.Analysis.exists_lipschitzWith_weak_fderiv_comp_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

open MeasureTheory Set
open FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.exists_lipschitzWith_weak_fderiv_comp_gradient_readable {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hULip : LipschitzWith L u)
    (hGradLip : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (a : Fin n) :
    ∃ C : NNReal,
      LipschitzWith C (fun x => fderiv ℝ W (gradient u x)
        (EuclideanSpace.basisFun (Fin n) ℝ a)) ∧
      ∀ j : Fin n,
        HasWeakDerivAlong
          (fun x => fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
          (fun x => ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp
            (fun x => ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by sorry
