-- Prove2me | Theorems.Thm_Galvin_dinitz
-- name    : Galvin.dinitz
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:13:57.920867+00:00
-- url     : https://prove2.me/theorems/d4399287-7f7d-47d3-b25c-143a173fcd89
-- title:
--   Galvin: dinitz
-- statement:
--   **The Dinitz problem** (Galvin 1995). If every cell of an `n × n` array has a list of at least
--   `n` symbols, there is a choice of one symbol from each list with all symbols in each row distinct
--   and all symbols in each column distinct.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Galvin.lean#L64-L114
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Galvin.lean#L64-L114

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

theorem Galvin.dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ (lists i j).card) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by sorry
