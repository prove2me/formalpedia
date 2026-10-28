-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_inner_gradient_gradient_inner_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_inner_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:52.25664+00:00
-- url     : https://prove2.me/theorems/b52d0520-93db-489b-81f1-06d18ce5c1bc
-- title:
--   Gradient Pairing Product-Rule Identity
-- statement:
--   This is a pointwise second-derivative identity for the drift term in the local Bochner calculation.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $U,f:E\to\mathbb R$ be respectively $C^2$, and let $x\in E$. Write $e_i$ for the fixed standard orthonormal basis of $E$. Then
--
--   $$
--   \left\langle \nabla f(x),\nabla\langle\nabla U,\nabla f\rangle(x)\right\rangle
--   =
--   D^2U(x)(\nabla f(x),\nabla f(x))
--   +\sum_i\sum_j \partial_iU(x)\,\partial_jf(x)\,D^2f(x)(e_i,e_j).
--   $$
--
--   The Hessian is represented by `bilinearIteratedFDerivTwo`, and the sums use `stdOrthonormalBasis ℝ E`. This technical identity is reusable in pointwise Bochner expansions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_gradient_gradient_inner {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
--       (x : E) :
--       ⟪gradient f x, gradient (fun y => ⟪gradient U y, gradient f y⟫) x⟫ =
--         bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) +
--           ∑ i, ∑ j, fderiv ℝ U x (stdOrthonormalBasis ℝ E i) *
--             fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
--             bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
--               (stdOrthonormalBasis ℝ E j)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a).
--
--   Previous: [`inner_gradient_gradient_laplacian`](https://prove2.me/theorems/7d81666e-8540-4388-b49c-344114d6512a) · Next: [`gammaTwo_eq_hessianSqStdBasis_add`](https://prove2.me/theorems/179f18c6-eedc-4764-b606-7f97a6d4c71b).
--
--   [Source excerpt, lines 264–271](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L264-L271) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L262-L286 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_inner`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic

open scoped ContDiff RealInnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_inner_readable {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (x : E) :
    ⟪gradient f x, gradient (fun y => ⟪gradient U y, gradient f y⟫) x⟫ =
      bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) +
        ∑ i, ∑ j, fderiv ℝ U x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
          bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
            (stdOrthonormalBasis ℝ E j) := by sorry
