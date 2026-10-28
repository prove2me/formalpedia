-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_filter_union_subset_readable
-- name    : FunctionalInequalities.Analysis.Tensor.card_filter_union_subset_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:59.377062+00:00
-- url     : https://prove2.me/theorems/cf9f5ea2-af4b-45a0-8c9a-cc4df00e06e9
-- title:
--   Counting Supersets of Two Fixed Subsets
-- statement:
--   This is a finite-set counting identity for two fixed subsets of equal size.
--
--   Let $\alpha$ be a type with decidable equality, let $U$ be a finite subset of $\alpha$, and let $d$ be a natural number. Assume:
--
--   1. $|U| = 3d$.
--   2. $F$ and $F'$ are $d$-element subsets of $U$.
--
--   Then the number of $2d$-element subsets $E$ of $U$ that contain $F \cup F'$ is
--
--   $$
--   \left|\{E \subseteq U : |E| = 2d \text{ and } F \cup F' \subseteq E\}\right|
--   = \binom{d + |F \cap F'|}{d}.
--   $$
--
--   The statement provides a reusable combinatorial count for supersets of a union of two $d$-element subsets, parameterized by the size of their intersection.
--
--   **Formalization Note** The finite-set families are represented by `Finset.powersetCard` and filtered using `Finset.filter`; the binomial coefficient is `Nat.choose`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem card_filter_union_subset (U : Finset α) {d : ℕ} (hU : U.card = 3 * d) {F F' : Finset α}
--       (hF : F ∈ U.powersetCard d) (hF' : F' ∈ U.powersetCard d) :
--       ((U.powersetCard (2 * d)).filter fun E => F ∪ F' ⊆ E).card =
--         (d + (F ∩ F').card).choose d
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Next: [`sum_choose_mul_card_filter_subset`](https://prove2.me/theorems/bdbd40ac-1a0c-4040-b7c6-4891fcad5583).
--
--   [Source excerpt, lines 64–67](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L64-L67) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L62-L166 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.card_filter_union_subset`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

variable {α : Type*} [DecidableEq α]

theorem FunctionalInequalities.Analysis.Tensor.card_filter_union_subset_readable (U : Finset α) {d : ℕ} (hU : U.card = 3 * d) {F F' : Finset α}
    (hF : F ∈ U.powersetCard d) (hF' : F' ∈ U.powersetCard d) :
    ((U.powersetCard (2 * d)).filter fun E => F ∪ F' ⊆ E).card =
      (d + (F ∩ F').card).choose d := by sorry
