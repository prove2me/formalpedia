-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_centeredDifference_nonneg_le_readable
-- name    : FunctionalInequalities.Analysis.centeredDifference_nonneg_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:40.099368+00:00
-- url     : https://prove2.me/theorems/9370319d-a121-4f26-8aa9-88be81cbf7e8
-- title:
--   Nonnegative Convex Centered Difference
-- statement:
--   This formalizes the centered-difference bounds used in the estimate associated with Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $u:\mathbb R^n\to\mathbb R$ be convex on the whole space, let $D\in\mathbb R$, and let $h\in\mathbb R^n$. Assume that for every $x$,
--
--   $$
--   u_h(x):=u(x+h)+u(x-h)-2u(x)\le D\|h\|^2.
--   $$
--
--   Then for every $x$,
--
--   $$
--   0\le \nu_h(x)\le D\|h\|^2,
--   $$
--
--   and also $0\le D\|h\|^2$. The declaration is `centeredDifference_nonneg_le_readable`. No differentiability or separate sign assumption on $D$ is made; the nonnegativity follows from convexity and the asserted upper bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem centeredDifference_nonneg_le {n : ℕ}
--       {u : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u)
--       {D : ℝ} (h : EuclideanSpace ℝ (Fin n))
--       (hw : ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
--       (∀ x, 0 ≤ u (x + h) + u (x - h) - 2 * u x ∧
--         u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) ∧
--         0 ≤ D * ‖h‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/SecondDifference`](https://prove2.me/theorems/5412cb80-13f4-48d5-ab21-d4aec90af26d).
--
--   Previous: [`centeredDifference_contDiff_lipschitz_gradient`](https://prove2.me/theorems/4365f234-8db7-4310-8445-040bbe73e928).
--
--   [Source excerpt, lines 839–845](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L839-L845) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L837-L871 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondDifference`, declaration `FunctionalInequalities.Analysis.centeredDifference_nonneg_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondDifference

open MeasureTheory Set Filter

theorem FunctionalInequalities.Analysis.centeredDifference_nonneg_le_readable {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u)
    {D : ℝ} (h : EuclideanSpace ℝ (Fin n))
    (hw : ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    (∀ x, 0 ≤ u (x + h) + u (x - h) - 2 * u x ∧
      u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) ∧
      0 ≤ D * ‖h‖ ^ 2 := by sorry
