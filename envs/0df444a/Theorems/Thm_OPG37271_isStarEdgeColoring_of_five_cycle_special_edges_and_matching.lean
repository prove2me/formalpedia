-- Prove2me | Theorems.Thm_OPG37271_isStarEdgeColoring_of_five_cycle_special_edges_and_matching
-- name    : OPG37271.isStarEdgeColoring_of_five_cycle_special_edges_and_matching
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:01:15.475955+00:00
-- url     : https://prove2.me/theorems/34424a93-8a87-4ddd-9b49-0a6cffd6de5f
-- title:
--   Star 7-edge-coloring from induced matchings and 5-cycle special-edge recoloring
-- statement:
--   Let $M \le G$ be colored in $\{3,4,5,6\}$ so that every color class of $M$ is an induced matching in $G$, and suppose $c$ restricts to a star edge-coloring on $G \setminus E(M)$ such that every edge outside $M \cup S$ uses $\{0,1,2\}$, while every special edge in $S$ avoids same-colored $M$-edges at edge-distances $1$ and $2$ in $G$. Then $c$ is a star $7$-edge-coloring of $G$.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, proof of Theorem 4.1(a) (5-cycle recoloring step).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem isStarEdgeColoring_of_five_cycle_special_edges_and_matching
    {V : Type u} {G M S : SimpleGraph V} (hMG : M ≤ G) (c : EdgeColoring G (Fin 7))
    (hrest_star : IsStarEdgeColoring
      (fun e => c ⟨e.1, SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le M.edgeSet) e.2⟩ :
        EdgeColoring (G.deleteEdges M.edgeSet) (Fin 7)))
    (hlow : ∀ x y (hxy : G.Adj x y), ¬ M.Adj x y → ¬ S.Adj x y → (c.get x y hxy).val < 3)
    (hM_ge3 : ∀ x y (hxy : M.Adj x y), 3 ≤ (c.get x y (hMG hxy)).val)
    (hM_induced : ∀ (x₁ y₁ x₂ y₂ : V) (h1 : M.Adj x₁ y₁) (h2 : M.Adj x₂ y₂),
      s(x₁, y₁) ≠ s(x₂, y₂) →
      c.get x₁ y₁ (hMG h1) = c.get x₂ y₂ (hMG h2) →
      x₁ ≠ x₂ ∧ x₁ ≠ y₂ ∧ y₁ ≠ x₂ ∧ y₁ ≠ y₂ ∧
        ¬ G.Adj x₁ x₂ ∧ ¬ G.Adj x₁ y₂ ∧ ¬ G.Adj y₁ x₂ ∧ ¬ G.Adj y₁ y₂)
    (hSM_dist1 : ∀ (v u w : V) (hvu : G.Adj v u),
      S.Adj v u → (hmw : M.Adj v w) → c.get v u hvu ≠ c.get v w (hMG hmw))
    (hSM_dist2 : ∀ (x₁ y₁ x₂ y₂ : V) (h1 : G.Adj x₁ y₁),
      S.Adj x₁ y₁ → (hm : M.Adj x₂ y₂) → G.Adj y₁ x₂ →
      c.get x₁ y₁ h1 ≠ c.get x₂ y₂ (hMG hm)) :
    IsStarEdgeColoring c := by sorry
end OPG37271
