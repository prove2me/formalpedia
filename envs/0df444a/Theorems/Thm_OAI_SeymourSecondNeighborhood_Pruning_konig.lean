-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_konig
-- name    : OAI.SeymourSecondNeighborhood.Pruning.konig
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-13T21:08:12.845246+00:00
-- url     : https://prove2.me/theorems/a50dea23-9d75-4c05-8d49-991005a52fac
-- title:
--   Kőnig's theorem, vertex-cover form: if every matching of a finite bipartite edge set $E\subseteq A\times B$ has at most $k$ edges, then $E$ has a vertex cover of size at most $k$
-- statement:
--   Let $A,B$ be types and $E\subseteq A\times B$ a finite set of edges of a bipartite graph. A *matching* is a subset $M\subseteq E$ on which both projections are injective, i.e. no two edges of $M$ share a left endpoint or a right endpoint. A *vertex cover* is a pair of finite sets $K_A\subseteq A$, $K_B\subseteq B$ such that every edge $(a,b)\in E$ has $a\in K_A$ or $b\in K_B$. The statement is K\H{o}nig's theorem in the form needed by the pruning lemma:
--   $$\text{if every matching }M\subseteq E\text{ satisfies }|M|\le k,\ \text{then there is a vertex cover with }|K_A|+|K_B|\le k .$$
--   Equivalently, the minimum size of a vertex cover of a finite bipartite graph equals the maximum size of a matching (the other inequality is trivial). It is used in the proof of the pruning lemma `OAI.SeymourSecondNeighborhood.Pruning.lemma_3_1`: the manuscript bounds a maximum matching of an augmented bipartite graph by $|Z|+|H|$ (`matching_bound`) and then takes a vertex cover of that size, whose original members are deleted. The theorem can be derived from Hall's marriage theorem (available in Mathlib as `Finset.all_card_le_biUnion_card_iff_exists_injective`) in its deficiency form.
--
--   **Formalization note.** No finiteness of $A$ or $B$ is assumed; only $E$ is a `Finset`. Matchings are subsets `M ⊆ E` with `Set.InjOn Prod.fst M` and `Set.InjOn Prod.snd M`.
-- source:
--   Statement extracted from Section 3 of OpenAI, *A proof of Seymour's second-neighborhood conjecture*, preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf; Kőnig's theorem: D. Kőnig, Matematikai és Fizikai Lapok 38 (1931) 116–119.

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood.Pruning

/-- **Kőnig's theorem** (vertex-cover form) for a finite bipartite graph given by its edge set
`E ⊆ A × B`. A *matching* is a set of edges `M ⊆ E` on which both projections are injective
(no two edges share a left endpoint or a right endpoint). If every matching in `E` has at most
`k` edges, then there is a *vertex cover* `KA ⊆ A`, `KB ⊆ B` (every edge of `E` has its left
endpoint in `KA` or its right endpoint in `KB`) with `|KA| + |KB| ≤ k`. -/
theorem konig {A B : Type*} (E : Finset (A × B)) (k : ℕ)
    (hk : ∀ M ⊆ E, Set.InjOn Prod.fst (M : Set (A × B)) →
      Set.InjOn Prod.snd (M : Set (A × B)) → M.card ≤ k) :
    ∃ KA : Finset A, ∃ KB : Finset B,
      (∀ e ∈ E, e.1 ∈ KA ∨ e.2 ∈ KB) ∧ KA.card + KB.card ≤ k := by
  sorry

end OAI.SeymourSecondNeighborhood.Pruning
