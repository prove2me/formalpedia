-- Prove2me | Theorems.Thm_GallaiEdmonds_image_supp_mk
-- name    : GallaiEdmonds.image_supp_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:19.338047+00:00
-- url     : https://prove2.me/theorems/377c6b9a-ee26-5079-b623-ebc7bc0dbb85
-- title:
--   Gallai Edmonds: image supp mk
-- statement:
--   The Gallai Edmonds construction uses the image supp mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L199-L206
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L199-L206

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

theorem GallaiEdmonds.image_supp_mk (H : SimpleGraph V) (W : Set V) (a : W) :
    Subtype.val '' ((H.induce W).connectedComponentMk a).supp = cc H W a.1 := by sorry
