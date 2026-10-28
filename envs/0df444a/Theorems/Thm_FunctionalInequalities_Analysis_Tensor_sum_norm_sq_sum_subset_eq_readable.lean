-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_norm_sq_sum_subset_eq_readable
-- name    : FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_subset_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:07.138444+00:00
-- url     : https://prove2.me/theorems/3f94b763-454c-46a7-862d-4d84329a2ef7
-- title:
--   BKL Subset-Sum Identity
-- statement:
--   This formalizes the equality in (25) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 2.2, p. 9.
--
--   Let $V$ be a real inner-product space, let $U$ be a finite set with $|U|=3d$, and let $x_F\in V$ be assigned to every $d$-element subset $F\subseteq U$. Then
--
--   $$
--   \sum_{\substack{E\subseteq U\\|E|=2d}}
--   \left\|\sum_{\substack{F\subseteq E\\|F|=d}}x_F\right\|^2
--   =
--   \sum_{s=0}^{d}\binom ds
--   \sum_{\substack{S\subseteq U\\|S|=s}}
--   \left\|\sum_{\substack{F\subseteq U,\ |F|=d\\S\subseteq F}}x_F\right\|^2.
--   $$
--
--   This is the central combinatorial norm identity used in the partial symmetrization estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_norm_sq_sum_subset_eq (U : Finset α) {d : ℕ} (hU : U.card = 3 * d)
--       (x : Finset α → V) :
--       ∑ E ∈ U.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2 =
--         ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
--           ∑ S ∈ U.powersetCard s, ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Supporting theorems: [`card_filter_union_subset`](https://prove2.me/theorems/cf9f5ea2-af4b-45a0-8c9a-cc4df00e06e9), [`sum_choose_mul_card_filter_subset`](https://prove2.me/theorems/bdbd40ac-1a0c-4040-b7c6-4891fcad5583), [`sum_norm_sq_sum_filter`](https://prove2.me/theorems/f152e5e8-eec5-438e-bbf0-9dca6ce16fe8).
--
--   Previous: [`sum_norm_sq_sum_filter`](https://prove2.me/theorems/f152e5e8-eec5-438e-bbf0-9dca6ce16fe8) · Next: [`sum_norm_sq_le_sum_norm_sq_sum_subset`](https://prove2.me/theorems/2747bdb8-2573-4a48-9d87-e05edbda390e).
--
--   [Source excerpt, lines 276–280](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L276-L280) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L272-L397 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_subset_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

open Finset
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {α : Type*} [DecidableEq α]

theorem FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_subset_eq_readable (U : Finset α) {d : ℕ} (hU : U.card = 3 * d)
    (x : Finset α → V) :
    ∑ E ∈ U.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2 =
      ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
        ∑ S ∈ U.powersetCard s, ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 := by sorry
