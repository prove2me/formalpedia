-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_laplacian_mul_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.laplacian_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:06.557292+00:00
-- url     : https://prove2.me/theorems/8f824324-1746-4ab8-ac22-419276d90dc5
-- title:
--   Product Rule for the Laplacian
-- statement:
--   This theorem is the pointwise product rule for the Euclidean Laplacian.
--
--   Let $E$ be a finite-dimensional complete real inner-product space, let $f,g:E\to\mathbb R$ be twice continuously differentiable, and let $x\in E$. Then
--
--   $$\Delta(fg)(x)=f(x)\Delta g(x)+g(x)\Delta f(x)+2\langle\nabla f(x),\nabla g(x)\rangle.$$
--
--   The identity is a local calculus tool and involves no measure, integrability, or curvature assumptions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem laplacian_mul {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
--       Laplacian.laplacian (fun y => f y * g y) x =
--         f x * Laplacian.laplacian g x + g x * Laplacian.laplacian f x +
--           2 * ⟪gradient f x, gradient g x⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a).
--
--   [Source excerpt, lines 594–597](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Calculus.lean#L594-L597) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Calculus.lean#L593-L620 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Calculus`, declaration `FunctionalInequalities.Analysis.BakryEmery.laplacian_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus

open scoped ContDiff RealInnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.laplacian_mul_readable {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    Laplacian.laplacian (fun y => f y * g y) x =
      f x * Laplacian.laplacian g x + g x * Laplacian.laplacian f x +
        2 * ⟪gradient f x, gradient g x⟫ := by sorry
