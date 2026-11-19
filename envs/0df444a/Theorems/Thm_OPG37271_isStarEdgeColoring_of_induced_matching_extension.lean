-- Prove2me | Theorems.Thm_OPG37271_isStarEdgeColoring_of_induced_matching_extension
-- name    : OPG37271.isStarEdgeColoring_of_induced_matching_extension
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T05:21:16.542548+00:00
-- url     : https://prove2.me/theorems/7ba00143-1541-441a-8004-1dcdb17c9429
-- title:
--   Extending a star 3-edge-coloring by 4 induced-matching color classes
-- statement:
--   Let $M$ be a spanning subgraph of a simple graph $G$, and let $c$ be a $7$-edge-coloring of $G$ such that $G \setminus E(M)$ uses only colors in $\{0,1,2\}$ and forms a star edge-coloring, while $M$ uses only colors in $\{3,4,5,6\}$ and each color class of $M$ is an induced matching in $G$. Then $c$ is a star $7$-edge-coloring of $G$.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, proof of Theorem 4.1(a) (4-colorable auxiliary graph step).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem isStarEdgeColoring_of_induced_matching_extension
    {V : Type u} {G M : SimpleGraph V} (hMG : M ≤ G) (c : EdgeColoring G (Fin 7))
    (hrest_star : IsStarEdgeColoring
      (fun e => c ⟨e.1, SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le M.edgeSet) e.2⟩ :
        EdgeColoring (G.deleteEdges M.edgeSet) (Fin 7)))
    (hrest_lt3 : ∀ x y (hxy : G.Adj x y), ¬ M.Adj x y → (c.get x y hxy).val < 3)
    (hM_ge3 : ∀ x y (hxy : M.Adj x y), 3 ≤ (c.get x y (hMG hxy)).val)
    (hM_induced : ∀ (x₁ y₁ x₂ y₂ : V) (h1 : M.Adj x₁ y₁) (h2 : M.Adj x₂ y₂),
      s(x₁, y₁) ≠ s(x₂, y₂) →
      c.get x₁ y₁ (hMG h1) = c.get x₂ y₂ (hMG h2) →
      x₁ ≠ x₂ ∧ x₁ ≠ y₂ ∧ y₁ ≠ x₂ ∧ y₁ ≠ y₂ ∧
        ¬ G.Adj x₁ x₂ ∧ ¬ G.Adj x₁ y₂ ∧ ¬ G.Adj y₁ x₂ ∧ ¬ G.Adj y₁ y₂) :
    IsStarEdgeColoring c := by sorry
end OPG37271
