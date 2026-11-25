-- Prove2me | Theorems.Thm_HaggkvistJanssen_exists_listEdgeColoring_complete
-- name    : HaggkvistJanssen.exists_listEdgeColoring_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:42:56.391037+00:00
-- url     : https://prove2.me/theorems/eb349dce-4a95-4e23-be9b-fa9335b5751e
-- title:
--   Haggkvist Janssen: exists list Edge Coloring complete
-- statement:
--   **Häggkvist–Janssen.** For lists of at least `|V|` colours on the edges of the complete graph
--   on `V`, there is a proper edge colouring (a colouring of the line graph) choosing every colour
--   from the list of its edge.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/Solution.lean#L26-L30
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/Solution.lean#L26-L30

module
public import Mathlib
public import Definitions.Def_LeanPool_ListEdgeColoringComplete
public import Definitions.Def_HaggkvistJanssen_Solution
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_exists_listEdgeColoring_complete

set_option autoImplicit true
@[expose] public section
public section
open HaggkvistJanssen

theorem HaggkvistJanssen.exists_listEdgeColoring_complete {V Color : Type*} [Fintype V]
    (lists : (⊤ : SimpleGraph V).edgeSet → Finset Color)
    (hLists : ∀ e, Fintype.card V ≤ (lists e).card) :
    ∃ coloring : (⊤ : SimpleGraph V).lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by sorry
