-- Prove2me | Theorems.Thm_ListEdgeColouring_galvin
-- name    : ListEdgeColouring.galvin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:33:03.760588+00:00
-- url     : https://prove2.me/theorems/02416537-8104-4f0e-9662-5c2e219271f3
-- title:
--   List Edge Colouring: galvin
-- statement:
--   **Galvin's theorem (1995).** If every edge of a finite bipartite graph `G` has a list of at
--   least `Δ(G)` colours, then `G` has a proper edge colouring choosing every colour from the list of
--   its edge.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Solution.lean#L46-L50
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Solution.lean#L46-L50

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Definitions.Def_GalvinMultigraph
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinDinitzSolution
public import Theorems.Thm_GalvinMultigraph_galvin
public import Theorems.Thm_Galvin_galvin

set_option autoImplicit true
@[expose] public section
public section
open ListEdgeColouring

theorem ListEdgeColouring.galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ (lists e).card) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by sorry
