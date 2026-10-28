-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_centeredDifference_contDiff_lipschitz_gradient_readable
-- name    : FunctionalInequalities.Analysis.centeredDifference_contDiff_lipschitz_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:47.315967+00:00
-- url     : https://prove2.me/theorems/4365f234-8db7-4310-8445-040bbe73e928
-- title:
--   Regularity of a Centered Second Difference
-- statement:
--   This formalizes the regularity estimate for a centered second difference, cited in the literature register as part of Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $u:\mathbb R^n\to\mathbb R$ be $C^1$, let $G\in[0,\infty)$, and suppose its gradient is $G$-Lipschitz. For any $h\in\mathbb R^n$, define
--
--   $$
--   v_h(x)=u(x+h)+u(x-h)-2u(x).
--   $$
--
--   Then $v_h$ is $C^1$ and its gradient is $4G$-Lipschitz:
--
--   $$
--   \operatorname{Lip}(\nabla v_h)\le 4G.
--   $$
--
--   The Lean declaration is `centeredDifference_contDiff_lipschitz_gradient_readable`. The result is an adapter for centered-difference estimates and does not assume convexity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem centeredDifference_contDiff_lipschitz_gradient {n : ℕ}
--       {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
--       {G : NNReal} (hG : LipschitzWith G (gradient u))
--       (h : EuclideanSpace ℝ (Fin n)) :
--       ContDiff ℝ 1 (fun x => u (x + h) + u (x - h) - 2 * u x) ∧
--         LipschitzWith (4 * G)
--           (gradient (fun x => u (x + h) + u (x - h) - 2 * u x))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/SecondDifference`](https://prove2.me/theorems/5412cb80-13f4-48d5-ab21-d4aec90af26d).
--
--   Previous: [`secondDifference_le_of_penalized_maxima`](https://prove2.me/theorems/a468a648-0c26-4aab-8d67-0b4ddb3e936a) · Next: [`centeredDifference_nonneg_le`](https://prove2.me/theorems/9370319d-a121-4f26-8aa9-88be81cbf7e8).
--
--   [Source excerpt, lines 781–787](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L781-L787) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L779-L834 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondDifference`, declaration `FunctionalInequalities.Analysis.centeredDifference_contDiff_lipschitz_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondDifference

theorem FunctionalInequalities.Analysis.centeredDifference_contDiff_lipschitz_gradient_readable {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    {G : NNReal} (hG : LipschitzWith G (gradient u))
    (h : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 1 (fun x => u (x + h) + u (x - h) - 2 * u x) ∧
      LipschitzWith (4 * G)
        (gradient (fun x => u (x + h) + u (x - h) - 2 * u x)) := by sorry
