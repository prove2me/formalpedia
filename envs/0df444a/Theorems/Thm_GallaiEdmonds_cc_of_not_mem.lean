-- Prove2me | Theorems.Thm_GallaiEdmonds_cc_of_not_mem
-- name    : GallaiEdmonds.cc_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:27.560063+00:00
-- url     : https://prove2.me/theorems/aa8f4c40-2939-4134-8f4e-b6ca9a9e7d5d
-- title:
--   Gallai Edmonds: cc of not mem
-- statement:
--   The Gallai Edmonds construction uses the cc of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L55-L56
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L55-L56

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

theorem GallaiEdmonds.cc_of_not_mem (hx : x ∉ W) : cc G W x = ∅ := by sorry
