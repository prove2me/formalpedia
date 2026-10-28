-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_contDiff_one_of_convexOn_of_differentiable_readable
-- name    : FunctionalInequalities.Analysis.contDiff_one_of_convexOn_of_differentiable_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:29.402264+00:00
-- url     : https://prove2.me/theorems/16eb9c9c-a99f-4109-be05-1626be515a47
-- title:
--   Differentiable Convex Functions Are C¹
-- statement:
--   This proves the finite-dimensional regularity fact that a differentiable convex function is $C^1$.
--
--   Let $E$ be a finite-dimensional real normed space and let $u:E\to\mathbb R$. If $u$ is convex on all of $E$ and differentiable everywhere, then
--
--   $$
--   u\in C^1(E),\qquad\text{that is,}\qquad \operatorname{ContDiff}_{\mathbb R}^{1}(u).
--   $$
--
--   The declaration is `contDiff_one_of_convexOn_of_differentiable_readable`. No quantitative Lipschitz estimate for the derivative is included, and finite dimensionality is essential to the stated result.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_one_of_convexOn_of_differentiable {E : Type*} [NormedAddCommGroup E]
--       [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
--       (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) :
--       ContDiff ℝ 1 u
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Next: [`subgradient_mem_of_ae_gradient_mem`](https://prove2.me/theorems/6f655218-b30e-46bf-be4f-c590531dd524).
--
--   [Source excerpt, lines 32–35](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L32-L35) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L30-L111 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.contDiff_one_of_convexOn_of_differentiable`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

theorem FunctionalInequalities.Analysis.contDiff_one_of_convexOn_of_differentiable_readable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) :
    ContDiff ℝ 1 u := by sorry
