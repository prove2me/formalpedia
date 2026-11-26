-- Prove2me | Theorems.Thm_GallaiEdmonds_oddComps_self
-- name    : GallaiEdmonds.oddComps_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:12.260019+00:00
-- url     : https://prove2.me/theorems/2fedeae3-abd2-47d3-baee-17cd8c6fa288
-- title:
--   Gallai Edmonds: odd Comps self
-- statement:
--   The Gallai Edmonds construction uses the odd Comps self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L150-L156
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L150-L156

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

theorem GallaiEdmonds.oddComps_self {K : Set V} (hK : K ∈ comps G W) (hodd : Odd K.ncard) :
    oddComps G K = {K} := by sorry
