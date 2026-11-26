-- Prove2me | Theorems.Thm_GallaiEdmonds_closed_compl
-- name    : GallaiEdmonds.closed_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:20.255804+00:00
-- url     : https://prove2.me/theorems/3ce307f7-16d3-4e8d-baab-b02383375326
-- title:
--   Gallai Edmonds: closed compl
-- statement:
--   The Gallai Edmonds construction uses the closed compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L158-L160
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L158-L160

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}

theorem GallaiEdmonds.closed_compl (hc : Closed G W W') : Closed G W (W \ W') := by sorry
