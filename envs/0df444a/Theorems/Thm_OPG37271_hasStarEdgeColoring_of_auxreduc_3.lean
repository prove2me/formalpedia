-- Prove2me | Theorems.Thm_OPG37271_hasStarEdgeColoring_of_auxreduc_3
-- name    : OPG37271.hasStarEdgeColoring_of_auxreduc_3
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:14:32.639178+00:00
-- url     : https://prove2.me/theorems/f4120e73-de96-4b20-938b-aa29c4ad4ffb
-- title:
--   Reducibility of Figure 1(c) (4-cycle with opposite degree-2 vertices)
-- statement:
--   Let $G$ be a finite subcubic simple graph containing an induced $4$-cycle $a_0 a_1 a_2 a_3 a_0$ whose opposite vertices $a_0$ and $a_2$ have degree at most $2$ in $G$. If $G - \{a_0,a_1,a_2,a_3\}$ admits a star $7$-edge-coloring, then so does $G$.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, Figure 1 (third configuration).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem hasStarEdgeColoring_of_auxreduc_3 {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (a₀ a₁ a₂ a₃ : V)
    (hnd : [a₀, a₁, a₂, a₃].Nodup)
    (h01 : G.Adj a₀ a₁) (h12 : G.Adj a₁ a₂) (h23 : G.Adj a₂ a₃) (h30 : G.Adj a₃ a₀)
    (ha₀ : (G.neighborSet a₀).encard ≤ 2) (ha₂ : (G.neighborSet a₂).encard ≤ 2)
    (hna13 : ¬ G.Adj a₁ a₃)
    (hc' : HasStarEdgeColoring
      (G.deleteEdges {e : Sym2 V | a₀ ∈ e ∨ a₁ ∈ e ∨ a₂ ∈ e ∨ a₃ ∈ e}) 7) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
