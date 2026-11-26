-- Prove2me | Theorems.Thm_GallaiEdmonds_oddComponents_ncard_eq
-- name    : GallaiEdmonds.oddComponents_ncard_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:59:00.155964+00:00
-- url     : https://prove2.me/theorems/21ca7b0a-c471-51a2-baac-8898d557350b
-- title:
--   Gallai Edmonds: odd Components ncard eq
-- statement:
--   The Gallai Edmonds construction uses the odd Components ncard eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L242-L244
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L242-L244

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

theorem GallaiEdmonds.oddComponents_ncard_eq [Finite V] (H : SimpleGraph V) (W : Set V) :
    (H.induce W).oddComponents.ncard = oddC H W := by sorry
