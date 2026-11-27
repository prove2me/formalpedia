-- Prove2me | Theorems.Thm_LefebvreVariations_tree_multiflow_packing_two_bins
-- name    : LefebvreVariations.tree_multiflow_packing_two_bins
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:18:07.987845+00:00
-- url     : https://prove2.me/theorems/644abc49-f695-5944-97e7-10ea9726cee6
-- title:
--   Lefebvre's variations, No. 248 — on a theme by Harb: items of total size at most 10 pack into two bins of size six
-- statement:
--   Let $I$ be a finite set of items with integer sizes $s_i\in\{1,2,\dots,6\}$ and total size
--   $$
--   \sum_{i\in I}s_i\ \le\ 4\cdot 2+2=10 .
--   $$
--   Then the items can be assigned to two bins, with no item split, so that each bin has total size at most $6$: there is $\beta:I\to\{0,1\}$ with $\sum_{\beta(i)=k}s_i\le 6$ for $k=0,1$.
--
--   This is the case $u=2$ of the packing lemma "items of sizes at most six and total size at most $4u+2$ fit into $u$ bins of size six", which the platform lists as open for every $u\ge1$ (the case $u=1$ only says that a total of at most six fits in one bin of size six).
--
--   **Formalization Note** The items are an arbitrary `Fintype`, `s : I → ℕ` with `1 ≤ s i ≤ 6`; the assignment is `β : I → Fin 2`, so empty bins are allowed. The hypothesis is `∑ i, s i ≤ 4 * 2 + 2`.
--
--   **Why this is a variation.** A variation on the open platform problem TreeMultiflow.lemma_A_1 (items of sizes in {1..6} and total at most 4u+2 pack into u bins of size six), played at u = 2 with the parent's statement restated verbatim, not imported. u = 1 is trivial (total at most six), so u = 2 is the first non-trivial size; the lemma for all u stays open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Elementary; the lemma is Lemma A.1 of Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, as quoted on the platform. Checked by exhaustive search over all multisets of sizes in {1..6} with total at most 10: every one packs into two bins of size six (and the same search succeeds for u = 1,...,5, totals up to 4u+2).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- The case `u = 2` of `TreeMultiflow.lemma_A_1` (the packing lemma, Harb, arXiv:2609.07949, Lemma A.1): every finite
collection of items with integer sizes in `{1, …, 6}` and total size at most `4·2 + 2 = 10` can be assigned to two bins
so that each bin has total size at most six (the case `u = 1` is the trivial one: total at most six).
Source: elementary; the statement is the lemma at `u = 2`. Checked by exhaustive search over all partitions of
the total `10` into parts at most six (every multiset of sizes packs into two bins; the same search succeeds for
`u = 1, …, 5`). -/
theorem tree_multiflow_packing_two_bins {I : Type*} [Fintype I] (s : I → ℕ)
    (hs : ∀ i, 1 ≤ s i ∧ s i ≤ 6) (htot : ∑ i, s i ≤ 4 * 2 + 2) :
    ∃ β : I → Fin 2, ∀ k : Fin 2, ∑ i ∈ Finset.univ.filter (fun i => β i = k), s i ≤ 6 := by
  sorry

end LefebvreVariations
