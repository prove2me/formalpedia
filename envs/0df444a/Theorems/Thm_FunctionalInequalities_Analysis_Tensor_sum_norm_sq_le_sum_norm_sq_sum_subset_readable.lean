-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_norm_sq_le_sum_norm_sq_sum_subset_readable
-- name    : FunctionalInequalities.Analysis.Tensor.sum_norm_sq_le_sum_norm_sq_sum_subset_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:58.932324+00:00
-- url     : https://prove2.me/theorems/2747bdb8-2573-4a48-9d87-e05edbda390e
-- title:
--   Subset-Sum Norm Inequality
-- statement:
--   This is the inequality form of the BKL subset-sum estimate.
--
--   Let $V$ be a real inner-product space, let $U$ be finite with $|U|=3d$, and let $x_F\in V$ be assigned to every $d$-element subset $F\subseteq U$. Then
--
--   $$
--   \sum_{\substack{F\subseteq U\\|F|=d}}\|x_F\|^2
--   \le
--   \sum_{\substack{E\subseteq U\\|E|=2d}}
--   \left\|\sum_{\substack{F\subseteq E\\|F|=d}}x_F\right\|^2.
--   $$
--
--   This inequality is the norm estimate extracted from the exact subset-sum identity and is used in the representation-theoretic symmetrization bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_norm_sq_le_sum_norm_sq_sum_subset (U : Finset α) {d : ℕ} (hU : U.card = 3 * d)
--       (x : Finset α → V) :
--       ∑ F ∈ U.powersetCard d, ‖x F‖ ^ 2 ≤
--         ∑ E ∈ U.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Supporting theorems: [`sum_norm_sq_sum_subset_eq`](https://prove2.me/theorems/3f94b763-454c-46a7-862d-4d84329a2ef7).
--
--   Previous: [`sum_norm_sq_sum_subset_eq`](https://prove2.me/theorems/3f94b763-454c-46a7-862d-4d84329a2ef7) · Next: [`exists_mem_fixingOutside_image_eq`](https://prove2.me/theorems/14b5df8e-d013-4b01-a20c-a437a2621fc7).
--
--   [Source excerpt, lines 401–404](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L401-L404) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L399-L458 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_norm_sq_le_sum_norm_sq_sum_subset`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {α : Type*} [DecidableEq α]

theorem FunctionalInequalities.Analysis.Tensor.sum_norm_sq_le_sum_norm_sq_sum_subset_readable (U : Finset α) {d : ℕ} (hU : U.card = 3 * d)
    (x : Finset α → V) :
    ∑ F ∈ U.powersetCard d, ‖x F‖ ^ 2 ≤
      ∑ E ∈ U.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2 := by sorry
