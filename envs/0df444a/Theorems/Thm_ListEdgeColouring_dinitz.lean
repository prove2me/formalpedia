-- Prove2me | Theorems.Thm_ListEdgeColouring_dinitz
-- name    : ListEdgeColouring.dinitz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:26:13.865248+00:00
-- url     : https://prove2.me/theorems/1e2cd8c7-110d-5e69-bc56-bd4f75105e5c
-- title:
--   List Edge Colouring: dinitz
-- statement:
--   **The Dinitz problem** (Galvin 1995). If every cell of an `n × n` array has a list of at least
--   `n` symbols, there is a choice of one symbol from each list with all symbols in each row distinct
--   and all symbols in each column distinct.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Solution.lean#L55-L59
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Solution.lean#L55-L59

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Definitions.Def_GalvinMultigraph
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinDinitzSolution
public import Theorems.Thm_Galvin_dinitz

set_option autoImplicit true
@[expose] public section
public section
open ListEdgeColouring

theorem ListEdgeColouring.dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ (lists i j).card) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by sorry
