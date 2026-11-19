-- Prove2me | Theorems.Thm_OPG37271_isStarEdgeColoring_insert_edge
-- name    : OPG37271.isStarEdgeColoring_insert_edge
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T04:39:27.122453+00:00
-- url     : https://prove2.me/theorems/374dc39c-d840-4d5a-9f62-ac6ff5e11817
-- title:
--   Single-edge star edge-coloring extension (Lemma 4.2(a))
-- statement:
--   Let $G$ be a simple graph, $e = uv$ an edge of $G$, and $c$ a $k$-edge-coloring of $G$. Suppose that the restriction of $c$ to $G - e$ is a star edge-coloring, and that $c(e') \ne c(e)$ for every edge $e' \ne e$ at edge-distance at most $2$ from $e$ (meaning $e'$ shares an endpoint with $e$ or has an endpoint adjacent to an endpoint of $e$). Then $c$ is a star edge-coloring of $G$.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Lemma 4.2(a).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem isStarEdgeColoring_insert_edge {V : Type u} {G : SimpleGraph V} {K : Type*}
    (u v : V) (huv : G.Adj u v) (c : EdgeColoring G K)
    (hc_rest : IsStarEdgeColoring (fun e => c ⟨e.1, SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le {s(u, v)}) e.2⟩ :
      EdgeColoring (G.deleteEdges {s(u, v)}) K))
    (hdist : ∀ (x y : V) (hxy : G.Adj x y), s(x, y) ≠ s(u, v) →
      (x = u ∨ x = v ∨ y = u ∨ y = v ∨ G.Adj u x ∨ G.Adj v x ∨ G.Adj u y ∨ G.Adj v y) →
      c.get x y hxy ≠ c.get u v huv) :
    IsStarEdgeColoring c := by sorry
end OPG37271
