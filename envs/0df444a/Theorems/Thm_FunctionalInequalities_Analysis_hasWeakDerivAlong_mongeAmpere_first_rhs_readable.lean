-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_mongeAmpere_first_rhs_readable
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_mongeAmpere_first_rhs_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:40.495585+00:00
-- url     : https://prove2.me/theorems/55f12f10-6c36-4776-96b3-387313b3b590
-- title:
--   Weak Derivative of the First Monge–Ampère Right-Hand Side
-- statement:
--   This is the weak derivative formula for the first Monge–Ampère right-hand side, corresponding to part of Lemma 2.4 of Letwin (arXiv:2607.24164v1).
--
--   Let $u$ be $C^1$ with Lipschitz $u$ and Lipschitz gradient, let $W$ be $C^2$, and let $T$ be a tensor of compact-local $L^2$ weak derivatives of the Hessian $H_u$. For every $i,j$, the function
--
--   $$
--   -\partial_i u+\sum_a H_{ia}\,\partial_aW(\nabla u)
--   $$
--
--   has weak derivative along $e_j$ equal to
--
--   $$
--   -H_{ji}+\sum_a\left(T_{jia}\,\partial_aW(\nabla u)
--   +H_{ia}\sum_b H_{jb}\,\partial_{ba}W(\nabla u)\right).
--   $$
--
--   The derivative density belongs locally to $L^2$ on every compact set. No $C^2$ regularity of $u$ is assumed.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--               hessianMatrix u x i a *
--                 ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
--           (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
--         ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--           MemLp
--             (fun x => -hessianMatrix u x j i +
--               ∑ a : Fin n,
--                 (T x j i a * fderiv ℝ W (gradient u x)
--                   (EuclideanSpace.basisFun (Fin n) ℝ a) +
--                 hessianMatrix u x i a *
--                   ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
--             2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution`](https://prove2.me/theorems/d20d941d-a690-4ebe-9a63-a346adf8dd16).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Selected supporting theorems: [`HasWeakDerivAlong.congr_ae`](https://prove2.me/theorems/feacd1e3-2d93-4444-8c84-fe52a0849220), [`HasWeakDerivAlong.mul_of_locally_bounded`](https://prove2.me/theorems/1133273b-c737-4c38-bf2a-2953cd23a941), [`exists_lipschitzWith_weak_fderiv_comp_gradient`](https://prove2.me/theorems/2b6867a4-8c8c-4420-8df5-b75bc2ce4bd7), [`hasWeakDerivAlong_finsetSum_mul`](https://prove2.me/theorems/2618f40b-2846-4d7d-9e77-e6c773de9cee), [`hasWeakDerivAlong_of_lipschitz`](https://prove2.me/theorems/b9fc0ec0-1bac-4138-9d6d-d21b20f114b9).
--
--   Previous: [`exists_lipschitzWith_weak_fderiv_comp_gradient`](https://prove2.me/theorems/2b6867a4-8c8c-4420-8df5-b75bc2ce4bd7) · Next: [`localLp_hessian_flux_trace_forcing`](https://prove2.me/theorems/0d14ed2a-5f26-4feb-914f-b0d0e87bf35c).
--
--   [Source excerpt, lines 407–418](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L407-L418) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L382-L460 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_mongeAmpere_first_rhs`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_mongeAmpere_first_rhs_readable {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ}
    {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
          ∑ a : Fin n, hessianMatrix u x i a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by sorry
