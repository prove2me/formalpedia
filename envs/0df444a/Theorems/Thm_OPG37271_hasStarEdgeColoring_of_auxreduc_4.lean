-- Prove2me | Theorems.Thm_OPG37271_hasStarEdgeColoring_of_auxreduc_4
-- name    : OPG37271.hasStarEdgeColoring_of_auxreduc_4
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:14:32.406401+00:00
-- url     : https://prove2.me/theorems/43c582af-608f-46af-a717-45563d95bd46
-- title:
--   Reducibility of Figure 1(d) (5-cycle with two non-adjacent degree-2 vertices)
-- statement:
--   Let $G$ be a finite subcubic simple graph containing a $5$-cycle $a_0 a_1 a_2 a_3 a_4 a_0$ with non-adjacent vertices $a_1, a_4$ of degree at most $2$ and no chords incident to $a_0$. If $G - \{a_0,a_1,a_2,a_3,a_4\}$ admits a star $7$-edge-coloring, then so does $G$.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, Figure 1 (fourth configuration).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem hasStarEdgeColoring_of_auxreduc_4 {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (a₀ a₁ a₂ a₃ a₄ : V)
    (hnd : [a₀, a₁, a₂, a₃, a₄].Nodup)
    (h01 : G.Adj a₀ a₁) (h12 : G.Adj a₁ a₂) (h23 : G.Adj a₂ a₃)
    (h34 : G.Adj a₃ a₄) (h40 : G.Adj a₄ a₀)
    (ha₁ : (G.neighborSet a₁).encard ≤ 2) (ha₄ : (G.neighborSet a₄).encard ≤ 2)
    (hna02 : ¬ G.Adj a₀ a₂) (hna03 : ¬ G.Adj a₀ a₃)
    (hc' : HasStarEdgeColoring
      (G.deleteEdges {e : Sym2 V | a₀ ∈ e ∨ a₁ ∈ e ∨ a₂ ∈ e ∨ a₃ ∈ e ∨ a₄ ∈ e}) 7) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
