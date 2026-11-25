-- Prove2me | Theorems.Thm_LeanPool_ListEdgeColoringComplete_exists_listEdgeColoring_complete
-- name    : LeanPool.ListEdgeColoringComplete.exists_listEdgeColoring_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:41:49.190281+00:00
-- url     : https://prove2.me/theorems/e28c8035-7146-470e-8e5a-eec3eb155d2a
-- title:
--   List Edge Coloring Complete: exists list Edge Coloring complete
-- statement:
--   **Häggkvist--Janssen.** The list chromatic index of the complete graph on `V` is at
--   most `|V|`: for arbitrary lists of at least `|V|` colours on the edges (from an arbitrary
--   colour type) there is a proper colouring of the line graph choosing from the lists.
--
--   Source: https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Main.lean#L80-L138
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Main.lean#L80-L138

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Main
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}

theorem LeanPool.ListEdgeColoringComplete.exists_listEdgeColoring_complete
    {V Color : Type*} [Fintype V]
    (lists : (⊤ : SimpleGraph V).edgeSet → Finset Color)
    (hLists : ∀ e, Fintype.card V ≤ (lists e).card) :
    ∃ coloring : (⊤ : SimpleGraph V).lineGraph.Coloring Color,
      ∀ e, coloring e ∈ lists e := by sorry
