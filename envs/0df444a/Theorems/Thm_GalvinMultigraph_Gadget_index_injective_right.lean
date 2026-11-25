-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_index_injective_right
-- name    : GalvinMultigraph.Gadget.index_injective_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:17:31.04554+00:00
-- url     : https://prove2.me/theorems/264674e4-3f7b-4e77-b936-a13c1d88ad9d
-- title:
--   Gadget: index injective right
-- statement:
--   The Gadget construction uses the index injective right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L174-L182
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L174-L182

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

theorem GalvinMultigraph.Gadget.index_injective_right (a : E → A) (b : E → B) (e : E) (j : Fin k) :
    Function.Injective (fun v : (graph a b).neighborSet (Sum.inr (Sum.inr (e, j))) =>
      index v.val) := by sorry
