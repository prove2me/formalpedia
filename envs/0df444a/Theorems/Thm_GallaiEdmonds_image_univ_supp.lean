-- Prove2me | Theorems.Thm_GallaiEdmonds_image_univ_supp
-- name    : GallaiEdmonds.image_univ_supp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:30.710985+00:00
-- url     : https://prove2.me/theorems/a28dcb28-b266-5c92-bea7-16e345c6d387
-- title:
--   Gallai Edmonds: image univ supp
-- statement:
--   The Gallai Edmonds construction uses the image univ supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L212-L220
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L212-L220

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

theorem GallaiEdmonds.image_univ_supp (H : SimpleGraph V) (W : Set V) :
    (fun c : (H.induce W).ConnectedComponent => Subtype.val '' c.supp) '' Set.univ =
      comps H W := by sorry
