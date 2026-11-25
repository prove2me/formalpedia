-- Prove2me | Theorems.Thm_GalvinMultigraph_maxDegree_le_of_proper
-- name    : GalvinMultigraph.maxDegree_le_of_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:24.134849+00:00
-- url     : https://prove2.me/theorems/6000451c-aac9-4bb4-b111-fccc86821abc
-- title:
--   Galvin Multigraph: max Degree le of proper
-- statement:
--   The palette size is bounded below by the actual multigraph maximum degree.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Main.lean#L123-L127
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Main.lean#L123-L127

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

theorem GalvinMultigraph.maxDegree_le_of_proper [Fintype A] [Fintype B] [Finite E] [Fintype Color]
    (a : E → A) (b : E → B) (c : E → Color) (hc : Proper a b c) :
    maxDegree a b ≤ Fintype.card Color := by sorry
