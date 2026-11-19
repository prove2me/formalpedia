-- Prove2me | Theorems.Thm_OPG37271_hasStarEdgeColoring_of_dist_le_two_lt
-- name    : OPG37271.hasStarEdgeColoring_of_dist_le_two_lt
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T04:43:37.252862+00:00
-- url     : https://prove2.me/theorems/e27f9edc-99d9-46bd-aabf-e9683b8c0a8f
-- title:
--   Star edge-coloring extension when fewer than k edges lie within distance 2
-- statement:
--   Let $G$ be a simple graph and $e = uv$ an edge of $G$. Suppose $G - e$ admits a star $k$-edge-coloring, and the set of edges in $G - e$ at edge-distance at most $2$ from $e$ can be covered by a finite set $S$ of cardinality $|S| < k$. Then $G$ also admits a star $k$-edge-coloring.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, immediate consequence of Lemma 4.2(a).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem hasStarEdgeColoring_of_dist_le_two_lt {V : Type u} {G : SimpleGraph V} {k : ℕ}
    (u v : V) (huv : G.Adj u v)
    (hc' : HasStarEdgeColoring (G.deleteEdges {s(u, v)}) k)
    (hbound : ∃ S : Finset (Sym2 V), S.card < k ∧
      ∀ x y : V, G.Adj x y → s(x, y) ≠ s(u, v) →
        (x = u ∨ x = v ∨ y = u ∨ y = v ∨ G.Adj u x ∨ G.Adj v x ∨ G.Adj u y ∨ G.Adj v y) →
        s(x, y) ∈ S) :
    HasStarEdgeColoring G k := by sorry
end OPG37271
