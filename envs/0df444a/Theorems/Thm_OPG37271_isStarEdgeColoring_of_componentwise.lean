-- Prove2me | Theorems.Thm_OPG37271_isStarEdgeColoring_of_componentwise
-- name    : OPG37271.isStarEdgeColoring_of_componentwise
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:01:10.497518+00:00
-- url     : https://prove2.me/theorems/fbc2a9c3-9fc6-4de2-8273-b9aa8d5baa8f
-- title:
--   Componentwise star edge-coloring of vertex-disjoint invariant subgraphs
-- statement:
--   If a simple graph $H$ is partitioned into vertex-disjoint edge-invariant components $\{v \mid \mathrm{comp}(v) = k\}$ and an edge-coloring $c$ of $H$ restricts to a star edge-coloring on each induced component, then $c$ is a star edge-coloring of $H$.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4.

import Definitions.Def_opg37271_star_edge_coloring

universe u
namespace OPG37271

theorem isStarEdgeColoring_of_componentwise
    {V : Type u} {ι : Type*} {H : SimpleGraph V} {K : Type*}
    (c : EdgeColoring H K) (comp : V → ι)
    (hcomp : ∀ {u v : V}, H.Adj u v → comp u = comp v)
    (hstar : ∀ k : ι, IsStarEdgeColoring
      (fun e => c ⟨Sym2.map Subtype.val e.1, by
        rcases e with ⟨e1, he1⟩
        induction e1 using Sym2.ind with
        | _ a b => exact he1⟩ :
        EdgeColoring (H.induce {v : V | comp v = k}) K)) :
    IsStarEdgeColoring c := by sorry
end OPG37271
