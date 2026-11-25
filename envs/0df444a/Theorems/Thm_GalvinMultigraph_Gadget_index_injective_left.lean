-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_index_injective_left
-- name    : GalvinMultigraph.Gadget.index_injective_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:17:33.375366+00:00
-- url     : https://prove2.me/theorems/105e8fb8-7e28-4fd6-8ded-c6f1244d3ca6
-- title:
--   Gadget: index injective left
-- statement:
--   The Gadget construction uses the index injective left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L164-L172
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L164-L172

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

theorem GalvinMultigraph.Gadget.index_injective_left (a : E → A) (b : E → B) (e : E) (i : Fin k) :
    Function.Injective (fun v : (graph a b).neighborSet (Sum.inl (Sum.inr (e, i))) =>
      index v.val) := by sorry
