-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_smooth_test_derivative_readable
-- name    : FunctionalInequalities.Analysis.smooth_test_derivative_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:46.635533+00:00
-- url     : https://prove2.me/theorems/a020d053-5b2e-45e7-bfaf-a25b6c53786c
-- title:
--   Derivative of a Weighted Coordinate Test
-- statement:
--   This is a technical coordinate identity for weighted test functions.
--
--   Let $n\in\mathbb N$, let $u,a,f:\mathbb R^n\to\mathbb R$ be functions on $\mathrm{EuclideanSpace}\ \mathbb R\ (\mathrm{Fin}\ n)$, with $u$ and $a$ of class $C^1$ and $f$ of class $C^2$. For $i,j\in\mathrm{Fin}\ n$ and $x\in\mathbb R^n$, the $j$-th coordinate derivative of the weighted test `weightedTest u a f i` is
--
--   $$\operatorname{coord}(\operatorname{weightedTest}(u,a,f,i))_j(x)=e^{-u(x)}\left(\operatorname{coord}(a)_j(x)\operatorname{coord}(f)_i(x)-a(x)\operatorname{coord}(u)_j(x)\operatorname{coord}(f)_i(x)+a(x)\,\operatorname{hessianMatrix}(f)(x)_{ji}\right).$$
--
--   This lemma supplies a pointwise product-and-chain-rule calculation used by the weak inverse-Hessian integration-by-parts identities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma smooth_test_derivative {n : ℕ}
--       {u a f : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : ContDiff ℝ 1 u) (ha : ContDiff ℝ 1 a)
--       (hf : ContDiff ℝ 2 f) (i j : Fin n)
--       (x : EuclideanSpace ℝ (Fin n)) :
--       coord (weightedTest u a f i) j x =
--         Real.exp (-u x) *
--           (coord a j x * coord f i x -
--             a x * coord u j x * coord f i x +
--             a x * hessianMatrix f x j i)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Previous: [`sum_inv_gradient_test_sub_chain_eq`](https://prove2.me/theorems/7266b246-03c7-419d-a30f-6d99183cc1fc) · Next: [`assemble_generator`](https://prove2.me/theorems/ecbe4dd5-bf64-4880-91be-e99fda5c9cf6).
--
--   [Source excerpt, lines 543–552](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L543-L552) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L543-L600 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak.0.FunctionalInequalities.Analysis.smooth_test_derivative`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

open FunctionalInequalities.Probability.Stein

lemma FunctionalInequalities.Analysis.smooth_test_derivative_readable {n : ℕ}
    {u a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (ha : ContDiff ℝ 1 a)
    (hf : ContDiff ℝ 2 f) (i j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.weightedTest u a f i) j x =
      Real.exp (-u x) *
        (FunctionalInequalities.Analysis.coord a j x * FunctionalInequalities.Analysis.coord f i x -
          a x * FunctionalInequalities.Analysis.coord u j x * FunctionalInequalities.Analysis.coord f i x +
          a x * hessianMatrix f x j i) := by sorry
