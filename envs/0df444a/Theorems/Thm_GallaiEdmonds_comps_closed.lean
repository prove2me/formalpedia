-- Prove2me | Theorems.Thm_GallaiEdmonds_comps_closed
-- name    : GallaiEdmonds.comps_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:15.026966+00:00
-- url     : https://prove2.me/theorems/03b846dc-c746-5026-aefb-51b2611e8f0f
-- title:
--   Gallai Edmonds: comps closed
-- statement:
--   The Gallai Edmonds construction uses the comps closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L120-L122
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L120-L122

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

theorem GallaiEdmonds.comps_closed {K : Set V} (hK : K ∈ comps G W) : Closed G W K := by sorry
