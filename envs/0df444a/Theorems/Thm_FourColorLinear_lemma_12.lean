-- Prove2me | Theorems.Thm_FourColorLinear_lemma_12
-- name    : FourColorLinear.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:23.335196+00:00
-- url     : https://prove2.me/theorems/873a3ca4-a79f-4e8b-8f0a-ee1a89e02028
-- title:
--   Lemma 12 — at most $6q-10$ white vertices in a plane bipartite graph with $q$ black vertices
-- statement:
--   Let $G$ be a simple planar bipartite graph with $q$ black and any number of white vertices. Suppose that every white vertex has a black neighbour and no two white vertices have the same set of black neighbours. Then the number of white vertices is at most $2^q-1$ if $q\le 2$, at most $6q-10$ if $q\ge3$, and hence at most $6q$ in every case.
--
--   This is the bound behind the count of main configuration types (p.20): the configurations touching a batch of $k$ Kempe chains realize $O(k)$ touch-sets.
--
--   Differences from the source:
--   - reading: "the number of white vertices is within a constant factor of the number of black vertices" → an upper bound only, with the numbers of the proof; reason: q black vertices and no white vertex satisfy the hypotheses, so only the upper direction can be claimed
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), Lemma 12 and its proof, p.21

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace FourColorLinear

/-- Lemma 12 of arXiv:2610.39753 (held version, sha256 4dce39c5…), p.21: "Consider a simple plane bipartite graph where the two partite sets
are black and white. Suppose that every white vertex has at least one black neighbor and no two white
vertices are adjacent to the same set of black vertices (think of this as a simple plane hypergraph
where the white vertices define the hyperedges). Then the number of white vertices is within a constant
factor of the number of black vertices."

**Formalization Note** With the proof's numbers: at most `2^q − 1` white vertices for `q ≤ 2` and
"q + 3q − 6 + 2q − 4 = 6q − 10" for `q ≥ 3`, so at most `6q`. Only the upper direction is a claim: `q`
black and no white vertices satisfy the hypotheses. -/
theorem lemma_12 {Black White : Type} [Fintype Black] [Fintype White]
    (G : SimpleGraph (Black ⊕ White)) (hG : RobertsonSeymour1986.GM5.IsPlanar G)
    (hb : ∀ x y : Black, ¬ G.Adj (.inl x) (.inl y)) (hw : ∀ x y : White, ¬ G.Adj (.inr x) (.inr y))
    (hne : ∀ x : White, ∃ y : Black, G.Adj (.inr x) (.inl y))
    (hdist : ∀ x x' : White, (∀ y : Black, G.Adj (.inr x) (.inl y) ↔ G.Adj (.inr x') (.inl y)) → x = x') :
    (Fintype.card Black ≤ 2 → Fintype.card White ≤ 2 ^ Fintype.card Black - 1) ∧
    (3 ≤ Fintype.card Black → Fintype.card White ≤ 6 * Fintype.card Black - 10) ∧
    Fintype.card White ≤ 6 * Fintype.card Black := by sorry

end FourColorLinear
