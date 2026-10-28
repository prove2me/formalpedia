-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_lipschitzWith_gradient_of_second_difference_le_readable
-- name    : FunctionalInequalities.Analysis.lipschitzWith_gradient_of_second_difference_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:48.962238+00:00
-- url     : https://prove2.me/theorems/b83dfd5c-be3e-4ba7-94af-eada55e6bd84
-- title:
--   Lipschitz Gradient from a Second-Difference Bound
-- statement:
--   Let $E$ be a complete real inner-product normed space, let $u:E\to\mathbb R$ be convex and differentiable, and let $C\ge0$. If for every $x,h\in E$,
--
--   $$u(x+h)+u(x-h)-2u(x)\le C\|h\|^2,$$
--
--   then the gradient is globally Lipschitz with constant $4C$ (represented in Lean by `Real.toNNReal (4 * C)`):
--
--   $$\|\nabla u(x)-\nabla u(y)\|\le4C\|x-y\|.$$
--
--   This is the standard $C^{1,1}$ consequence of the centered second-difference estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lipschitzWith_gradient_of_second_difference_le {E : Type*} [NormedAddCommGroup E]
--       [InnerProductSpace ℝ E] [CompleteSpace E] {u : E → ℝ} {C : ℝ}
--       (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) (hC : 0 ≤ C)
--       (hsd : ∀ x h : E, u (x + h) + u (x - h) - 2 * u x ≤ C * ‖h‖ ^ 2) :
--       LipschitzWith (Real.toNNReal (4 * C)) (gradient u)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/SecondDifference`](https://prove2.me/theorems/5412cb80-13f4-48d5-ab21-d4aec90af26d).
--
--   Next: [`sd_penalized_estimate`](https://prove2.me/theorems/c0c70d58-7455-4740-861b-7db419ae03b7).
--
--   [Source excerpt, lines 217–221](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L217-L221) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L215-L480 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondDifference`, declaration `FunctionalInequalities.Analysis.lipschitzWith_gradient_of_second_difference_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondDifference

theorem FunctionalInequalities.Analysis.lipschitzWith_gradient_of_second_difference_le_readable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {u : E → ℝ} {C : ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) (hC : 0 ≤ C)
    (hsd : ∀ x h : E, u (x + h) + u (x - h) - 2 * u x ≤ C * ‖h‖ ^ 2) :
    LipschitzWith (Real.toNNReal (4 * C)) (gradient u) := by sorry
