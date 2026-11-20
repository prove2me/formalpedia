-- Prove2me | Theorems.Thm_OPG37271_hasStarEdgeColoring_of_auxreduc_1
-- name    : OPG37271.hasStarEdgeColoring_of_auxreduc_1
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:14:30.641185+00:00
-- url     : https://prove2.me/theorems/3d7c73a1-cbca-428c-a206-3f5cae7a7284
-- title:
--   Reducibility of Figure 1(a) (4-cycle with stem and two degree-2 vertices)
-- statement:
--   Let $G$ be a finite subcubic simple graph containing distinct vertices $a_0,a_1,a_2,a_3,a_4$ forming a $4$-cycle $a_0 a_1 a_2 a_3 a_0$ plus a stem edge $a_2 a_4$, with $\deg_G(a_0) \le 2$, $\deg_G(a_4) \le 2$, and no chords among $\{a_1,a_3,a_4\}$. If $G - \{a_0,a_1,a_2,a_3,a_4\}$ admits a star $7$-edge-coloring, then so does $G$.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, Figure 1 (first configuration).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem hasStarEdgeColoring_of_auxreduc_1 {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (a₀ a₁ a₂ a₃ a₄ : V)
    (hnd : [a₀, a₁, a₂, a₃, a₄].Nodup)
    (h01 : G.Adj a₀ a₁) (h12 : G.Adj a₁ a₂) (h23 : G.Adj a₂ a₃) (h30 : G.Adj a₃ a₀)
    (h24 : G.Adj a₂ a₄)
    (ha₀ : (G.neighborSet a₀).encard ≤ 2) (ha₄ : (G.neighborSet a₄).encard ≤ 2)
    (hna13 : ¬ G.Adj a₁ a₃) (hna14 : ¬ G.Adj a₁ a₄) (hna34 : ¬ G.Adj a₃ a₄)
    (hc' : HasStarEdgeColoring
      (G.deleteEdges {e : Sym2 V | a₀ ∈ e ∨ a₁ ∈ e ∨ a₂ ∈ e ∨ a₃ ∈ e ∨ a₄ ∈ e}) 7) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
