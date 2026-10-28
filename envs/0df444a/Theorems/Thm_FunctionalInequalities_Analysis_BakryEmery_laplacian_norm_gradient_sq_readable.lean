-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_laplacian_norm_gradient_sq_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.laplacian_norm_gradient_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:52.265919+00:00
-- url     : https://prove2.me/theorems/f7c7e14e-684d-4c0f-a364-0f0a923ffcc2
-- title:
--   Laplacian of the Squared Gradient Norm
-- statement:
--   This is the pointwise expansion of the Laplacian of the squared gradient norm.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $f:E\to\mathbb R$ be $C^3$, and let $x\in E$. For the fixed standard orthonormal basis $(e_i)$,
--
--   $$
--   \Delta\|\nabla f\|^2(x)
--   =
--   2\sum_i\sum_j\bigl(D^2f(x)(e_i,e_j)\bigr)^2
--   +2\sum_j \partial_jf(x)\sum_i\partial_i\partial_i\partial_jf(x).
--   $$
--
--   The Hessian terms are expressed by `bilinearIteratedFDerivTwo`; the third-order terms are retained explicitly. The identity is a technical component of the local Bochner identity and includes the dimension-zero case.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem laplacian_norm_gradient_sq {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
--       Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x =
--         2 * ∑ i, ∑ j,
--             (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
--               (stdOrthonormalBasis ℝ E j)) ^ 2 +
--           2 * ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
--             ∑ i, fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
--               (stdOrthonormalBasis ℝ E i)) x (stdOrthonormalBasis ℝ E i)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a).
--
--   Next: [`inner_gradient_gradient_laplacian`](https://prove2.me/theorems/7d81666e-8540-4388-b49c-344114d6512a).
--
--   [Source excerpt, lines 208–215](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L208-L215) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L207-L242 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.laplacian_norm_gradient_sq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.laplacian_norm_gradient_sq_readable {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
    Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x =
      2 * ∑ i, ∑ j,
          (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
            (stdOrthonormalBasis ℝ E j)) ^ 2 +
        2 * ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
          ∑ i, fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
            (stdOrthonormalBasis ℝ E i)) x (stdOrthonormalBasis ℝ E i) := by sorry
