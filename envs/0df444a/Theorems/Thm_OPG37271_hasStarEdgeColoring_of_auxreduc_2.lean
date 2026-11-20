-- Prove2me | Theorems.Thm_OPG37271_hasStarEdgeColoring_of_auxreduc_2
-- name    : OPG37271.hasStarEdgeColoring_of_auxreduc_2
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:14:34.908753+00:00
-- url     : https://prove2.me/theorems/6c1358a4-b816-4f69-8c5b-3d74860c286a
-- title:
--   Reducibility of Figure 1(b) (triangle with two degree-2 stems)
-- statement:
--   Let $G$ be a finite subcubic simple graph containing distinct vertices $a_0,a_1,a_2,a_3,a_4$ forming a triangle $a_0 a_1 a_2 a_0$ with stem edges $a_1 a_3$ and $a_2 a_4$, where $\deg_G(a_3) \le 2$, $\deg_G(a_4) \le 2$, and $\{a_0,a_3,a_4\}$ is independent. If $G - \{a_0,a_1,a_2,a_3,a_4\}$ admits a star $7$-edge-coloring, then so does $G$.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, Figure 1 (second configuration).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem hasStarEdgeColoring_of_auxreduc_2 {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (a₀ a₁ a₂ a₃ a₄ : V)
    (hnd : [a₀, a₁, a₂, a₃, a₄].Nodup)
    (h01 : G.Adj a₀ a₁) (h12 : G.Adj a₁ a₂) (h20 : G.Adj a₂ a₀)
    (h13 : G.Adj a₁ a₃) (h24 : G.Adj a₂ a₄)
    (ha₃ : (G.neighborSet a₃).encard ≤ 2) (ha₄ : (G.neighborSet a₄).encard ≤ 2)
    (hna03 : ¬ G.Adj a₀ a₃) (hna04 : ¬ G.Adj a₀ a₄) (hna34 : ¬ G.Adj a₃ a₄)
    (hc' : HasStarEdgeColoring
      (G.deleteEdges {e : Sym2 V | a₀ ∈ e ∨ a₁ ∈ e ∨ a₂ ∈ e ∨ a₃ ∈ e ∨ a₄ ∈ e}) 7) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
