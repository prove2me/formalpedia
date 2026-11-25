-- Prove2me | Theorems.Thm_GalvinMultigraph_degreeB_le_maxDegree
-- name    : GalvinMultigraph.degreeB_le_maxDegree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:20:43.300534+00:00
-- url     : https://prove2.me/theorems/a7fe3f6f-f088-43a4-be0d-b1d5ab6af81d
-- title:
--   Galvin Multigraph: degree B le max Degree
-- statement:
--   The Galvin Multigraph construction uses the degree B le max Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Main.lean#L41-L44
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Main.lean#L41-L44

module
public import Definitions.Def_GalvinMultigraph_Gadget
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinMultigraph_Main
set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph
open Finset
variable {A B E Color : Type*}

theorem GalvinMultigraph.degreeB_le_maxDegree [Fintype A] [Fintype B] (a : E → A) (b : E → B) (y : B) :
    Nat.card {e // b e = y} ≤ maxDegree a b := by sorry
