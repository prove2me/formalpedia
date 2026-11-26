-- Prove2me | Theorems.Thm_GallaiEdmonds_image_odd_supp
-- name    : GallaiEdmonds.image_odd_supp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:47.645858+00:00
-- url     : https://prove2.me/theorems/09e9cddf-dea8-4786-87f7-c488ce85413a
-- title:
--   Gallai Edmonds: image odd supp
-- statement:
--   The Gallai Edmonds construction uses the image odd supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L222-L235
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L222-L235

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

theorem GallaiEdmonds.image_odd_supp [Finite V] (H : SimpleGraph V) (W : Set V) :
    (fun c : (H.induce W).ConnectedComponent => Subtype.val '' c.supp) ''
      (H.induce W).oddComponents = oddComps H W := by sorry
