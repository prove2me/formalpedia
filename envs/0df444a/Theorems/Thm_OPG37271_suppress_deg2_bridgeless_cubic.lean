-- Prove2me | Theorems.Thm_OPG37271_suppress_deg2_bridgeless_cubic
-- name    : OPG37271.suppress_deg2_bridgeless_cubic
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:16:16.644163+00:00
-- url     : https://prove2.me/theorems/772728e0-b0af-4367-bfe9-c883c1a40c3d
-- title:
--   Degree-2 Vertex Suppression Preserves 3-Regularity and Bridgelessness
-- statement:
--   Let $G$ be a finite bridgeless simple graph in which every vertex has degree $2$ or $3$, with no adjacent degree-$2$ vertices, no triangle containing a degree-$2$ vertex, and no $4$-cycle with opposite degree-$2$ vertices. Then suppressing all degree-$2$ vertices produces a simple, $3$-regular, bridgeless graph $G'$ on the degree-$3$ vertices of $G$.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Proof of Theorem 4.1(a).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem suppress_deg2_bridgeless_cubic
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ v : V, (G.neighborSet v).encard = 2 ∨ (G.neighborSet v).encard = 3)
    (hbridge : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v)
    (hnoadj2 : ∀ u v : V, G.Adj u v →
      ¬ ((G.neighborSet u).encard ≤ 2 ∧ (G.neighborSet v).encard ≤ 2))
    (hnotri2 : ∀ x y z : V, G.Adj x z → G.Adj y z → G.Adj x y →
      ¬ (G.neighborSet z).encard ≤ 2)
    (hno4cyc2 : ∀ z₁ z₂ x y : V, z₁ ≠ z₂ → x ≠ y →
      (G.neighborSet z₁).encard = 2 → (G.neighborSet z₂).encard = 2 →
      G.Adj x z₁ → G.Adj y z₁ → G.Adj x z₂ → G.Adj y z₂ → False) :
    ∃ G' : SimpleGraph {v : V // (G.neighborSet v).encard = 3},
      (∀ u w : {v : V // (G.neighborSet v).encard = 3},
        G'.Adj u w ↔ u ≠ w ∧
          (G.Adj u.1 w.1 ∨ ∃ z : V, (G.neighborSet z).encard = 2 ∧ G.Adj u.1 z ∧ G.Adj w.1 z)) ∧
      (∀ u : {v : V // (G.neighborSet v).encard = 3},
        (G'.neighborSet u).encard = 3) ∧
      (∀ u w : {v : V // (G.neighborSet v).encard = 3},
        G'.Adj u w → (G'.deleteEdges {s(u, w)}).Reachable u w) := by sorry
end OPG37271
