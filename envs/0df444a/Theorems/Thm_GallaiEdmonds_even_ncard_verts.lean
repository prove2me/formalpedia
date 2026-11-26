-- Prove2me | Theorems.Thm_GallaiEdmonds_even_ncard_verts
-- name    : GallaiEdmonds.even_ncard_verts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:59:12.80384+00:00
-- url     : https://prove2.me/theorems/8da618a4-54b8-5005-a97f-29bf0f28479b
-- title:
--   Gallai Edmonds: even ncard verts
-- statement:
--   The Gallai Edmonds construction uses the even ncard verts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L47-L49
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L47-L49

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}

theorem GallaiEdmonds.even_ncard_verts [Finite V] {M : G.Subgraph} (hM : M.IsMatching) :
    Even M.verts.ncard := by sorry
