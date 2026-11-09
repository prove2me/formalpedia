-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_lemma_3_2_i
-- name    : KColoringFaster.ListBootstrap.lemma_3_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:55.696198+00:00
-- url     : https://prove2.me/theorems/a15c9848-bb3b-4ce0-b0fd-1ae1e1069c1f
-- title:
--   Lemma 3.2 (i) — deleting edges between disjoint lists (rule (N))
-- statement:
--   Let $G$ be a graph on $\{0,\dots,n-1\}$ with lists $L$.
--
--   1. Deleting an edge $uv$ with $L(u)\cap L(v)=\emptyset$ preserves exactly the set of list colorings: for every map $c$,
--   $$c \text{ is a list coloring of } (G-uv,L)\iff c \text{ is a list coloring of } (G,L).$$
--   2. Repeating this operation any finite number of times (the process (N)) preserves exactly the set of list colorings; the lists are not changed, in particular not enlarged.
--   3. The process (N) ends at the graph $\mathrm{norm}_L(G)$ obtained by deleting all edges with disjoint lists: this graph is reachable by such deletions, it has no edge whose endpoints have disjoint lists, and every graph reachable by such deletions in which no such edge is left equals $\mathrm{norm}_L(G)$.
--
--   The general algorithm of §5 uses only this rule (p. 23: "exhaust rule (N) from Lemma 3.2").
--
--   Differences from the source:
--   - encoding: "(N) the process of repeating this operation as long as such an edge exists" → finite sequences of single deletions, with the end state characterized as $\mathrm{norm}_L(G)$; reason: the lists do not change, so the process has a unique end state
--   - generalization: nonempty lists → lists may be empty; reason: the source's instances are included
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 8, Lemma 3.2 (i) and its last sentence

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Normalization

open Classical

namespace KColoringFaster.ListBootstrap

/-- Lemma 3.2 (Normalization), part (i), p. 8. Let `G` be a graph on `Fin n` with lists `L`.
1. Deleting an edge `uv` with `L u ∩ L v = ∅` preserves exactly the set of list colorings.
2. Every finite sequence of such deletions (the process (N)) preserves exactly the set of list
   colorings; the lists are never changed, in particular never enlarged.
3. The process (N) ends at `normGraph L G` (all such edges deleted): it is reachable, it has no edge
   with disjoint lists, and every graph reachable by such deletions with no edge left to delete is
   `normGraph L G`. -/
theorem lemma_3_2_i :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (L : Fin n → Finset ℕ) (u v : Fin n),
      G.Adj u v → Disjoint (L u) (L v) →
        ∀ c, IsListColoringOf (G.deleteEdges {s(u, v)}) L c ↔ IsListColoringOf G L c) ∧
    (∀ (n : ℕ) (L : Fin n → Finset ℕ) (G G' : SimpleGraph (Fin n)),
      Relation.ReflTransGen (NStep L) G G' →
        ∀ c, IsListColoringOf G' L c ↔ IsListColoringOf G L c) ∧
    (∀ (n : ℕ) (L : Fin n → Finset ℕ) (G : SimpleGraph (Fin n)),
      Relation.ReflTransGen (NStep L) G (normGraph L G) ∧
      (∀ u v, (normGraph L G).Adj u v → ¬ Disjoint (L u) (L v)) ∧
      ∀ G', Relation.ReflTransGen (NStep L) G G' →
        (∀ u v, G'.Adj u v → ¬ Disjoint (L u) (L v)) → G' = normGraph L G) := by sorry

end KColoringFaster.ListBootstrap
