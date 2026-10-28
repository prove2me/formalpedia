-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_inner_gradient_gradient_laplacian_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_laplacian_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:57.699194+00:00
-- url     : https://prove2.me/theorems/7d81666e-8540-4388-b49c-344114d6512a
-- title:
--   Gradient Pairing with the Laplacian
-- statement:
--   This is a pointwise third-order derivative identity.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $f:E\to\mathbb R$ be $C^3$, and let $x\in E$. With $e_i$ denoting the fixed standard orthonormal basis,
--
--   $$
--   \langle\nabla f(x),\nabla(\Delta f)(x)\rangle
--   =
--   \sum_j \partial_jf(x)\sum_i \partial_i\partial_i\partial_j f(x).
--   $$
--
--   In the formal expression, the inner sum is written by applying the derivative to $y\mapsto \partial_i\partial_j f(y)$ in the direction $e_i$; equality uses commutation of third derivatives. This is an auxiliary identity for local Bochner formulas.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_gradient_gradient_laplacian {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
--       ⟪gradient f x, gradient (Laplacian.laplacian f) x⟫ =
--         ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
--           ∑ i, fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
--             (stdOrthonormalBasis ℝ E i)) x (stdOrthonormalBasis ℝ E i)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a).
--
--   Previous: [`laplacian_norm_gradient_sq`](https://prove2.me/theorems/f7c7e14e-684d-4c0f-a364-0f0a923ffcc2) · Next: [`inner_gradient_gradient_inner`](https://prove2.me/theorems/b52d0520-93db-489b-81f1-06d18ce5c1bc).
--
--   [Source excerpt, lines 245–249](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L245-L249) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L244-L260 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_laplacian`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic

open scoped ContDiff RealInnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_laplacian_readable {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
    ⟪gradient f x, gradient (Laplacian.laplacian f) x⟫ =
      ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
        ∑ i, fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
          (stdOrthonormalBasis ℝ E i)) x (stdOrthonormalBasis ℝ E i) := by sorry
