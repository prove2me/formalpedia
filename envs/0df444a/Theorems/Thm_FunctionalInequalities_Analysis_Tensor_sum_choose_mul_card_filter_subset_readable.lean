-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_choose_mul_card_filter_subset_readable
-- name    : FunctionalInequalities.Analysis.Tensor.sum_choose_mul_card_filter_subset_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:57.666982+00:00
-- url     : https://prove2.me/theorems/bdbd40ac-1a0c-4040-b7c6-4891fcad5583
-- title:
--   Vandermonde Count for Subsets of an Intersection
-- statement:
--   This is a finite-set identity expressing a Vandermonde convolution for two fixed subsets.
--
--   Let $\alpha$ be a type with decidable equality, let $U$ be a finite subset of $\alpha$, let $d$ be a natural number, and let $F,F'$ be $d$-element subsets of $U$. For each natural number $s$ from $0$ through $d$, count the $s$-element subsets $S$ of $U$ satisfying $S \subseteq F \cap F'$. Then
--
--   $$
--   \sum_{s=0}^{d} \binom{d}{s}
--   \left|\{S \subseteq U : |S|=s \text{ and } S \subseteq F \cap F'\}\right|
--   = \binom{d+|F \cap F'|}{d}.
--   $$
--
--   This identity is a reusable combinatorial summation formula, with the summands counting subsets of the intersection and weighting them by binomial coefficients.
--
--   **Formalization Note** The summation is implemented over `Finset.range (d + 1)`, and the counted families use `Finset.powersetCard` followed by `Finset.filter`; binomial coefficients are represented by `Nat.choose`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_choose_mul_card_filter_subset (U : Finset α) {d : ℕ} {F F' : Finset α}
--       (hF : F ∈ U.powersetCard d) (hF' : F' ∈ U.powersetCard d) :
--       ∑ s ∈ range (d + 1), d.choose s * ((U.powersetCard s).filter fun S => S ⊆ F ∩ F').card =
--         (d + (F ∩ F').card).choose d
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Previous: [`card_filter_union_subset`](https://prove2.me/theorems/cf9f5ea2-af4b-45a0-8c9a-cc4df00e06e9) · Next: [`sum_norm_sq_sum_filter`](https://prove2.me/theorems/f152e5e8-eec5-438e-bbf0-9dca6ce16fe8).
--
--   [Source excerpt, lines 196–199](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L196-L199) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L194-L218 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_choose_mul_card_filter_subset`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

open Finset
variable {α : Type*} [DecidableEq α]

theorem FunctionalInequalities.Analysis.Tensor.sum_choose_mul_card_filter_subset_readable (U : Finset α) {d : ℕ} {F F' : Finset α}
    (hF : F ∈ U.powersetCard d) (hF' : F' ∈ U.powersetCard d) :
    ∑ s ∈ range (d + 1), d.choose s * ((U.powersetCard s).filter fun S => S ⊆ F ∩ F').card =
      (d + (F ∩ F').card).choose d := by sorry
