-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_aEdge_injective
-- name    : GalvinMultigraph.Gadget.aEdge_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:19:27.88493+00:00
-- url     : https://prove2.me/theorems/2abbeab6-e313-4609-bef0-e6c2f7813845
-- title:
--   Gadget: a Edge injective
-- statement:
--   The Gadget construction uses the a Edge injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L314-L319
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L314-L319

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

theorem GalvinMultigraph.Gadget.aEdge_injective (a : E → A) (b : E → B) :
    Function.Injective (aEdge (k := k) a b) := by sorry
