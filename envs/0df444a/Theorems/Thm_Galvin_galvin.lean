-- Prove2me | Theorems.Thm_Galvin_galvin
-- name    : Galvin.galvin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:59.455984+00:00
-- url     : https://prove2.me/theorems/a2d8f072-a4cf-4ea1-bb0a-d0252e42c6a7
-- title:
--   Galvin: galvin
-- statement:
--   **Galvin's theorem (1995).** If every edge of a finite bipartite graph `G` has a list of at
--   least `Δ(G)` colours, then `G` has a proper edge colouring choosing every colour from the list of
--   its edge.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Galvin.lean#L51-L59
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Galvin.lean#L51-L59

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Definitions.Def_Konig_Basic
public import Definitions.Def_GalvinLib_Orientation
public import Definitions.Def_GalvinLib_Galvin
set_option autoImplicit true
@[expose] public section
public section
open Galvin

theorem Galvin.galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ (lists e).card) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by sorry
