-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_columnEdge_injective
-- name    : GalvinMultigraph.Gadget.columnEdge_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:17:00.079193+00:00
-- url     : https://prove2.me/theorems/b64e1a47-b71c-4e68-a8bc-e6cd1caf34db
-- title:
--   Gadget: column Edge injective
-- statement:
--   The Gadget construction uses the column Edge injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L136-L140
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L136-L140

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget
set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph GalvinMultigraph.Gadget
open Finset SimpleGraph
variable {A B E Color : Type*} {k : ℕ} [NeZero k]

theorem GalvinMultigraph.Gadget.columnEdge_injective (a : E → A) (b : E → B) (e : E) (j : Fin k) (hj : j ≠ 0) :
    Function.Injective (fun i => rowEdge a b e i j) := by sorry
