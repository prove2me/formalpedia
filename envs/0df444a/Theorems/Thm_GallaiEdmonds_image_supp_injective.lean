-- Prove2me | Theorems.Thm_GallaiEdmonds_image_supp_injective
-- name    : GallaiEdmonds.image_supp_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:50.098937+00:00
-- url     : https://prove2.me/theorems/a316ce72-c5dd-4187-9129-a4b820a8ce6b
-- title:
--   Gallai Edmonds: image supp injective
-- statement:
--   The Gallai Edmonds construction uses the image supp injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L208-L210
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L208-L210

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

theorem GallaiEdmonds.image_supp_injective (H : SimpleGraph V) (W : Set V) :
    Function.Injective fun c : (H.induce W).ConnectedComponent => Subtype.val '' c.supp := by sorry
