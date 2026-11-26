-- Prove2me | Theorems.Thm_GallaiEdmonds_cc_eq_of_closed
-- name    : GallaiEdmonds.cc_eq_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:06.284137+00:00
-- url     : https://prove2.me/theorems/a4a3f1ba-94a9-5ef3-9030-3bcdd230ef61
-- title:
--   Gallai Edmonds: cc eq of closed
-- statement:
--   The Gallai Edmonds construction uses the cc eq of closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L89-L92
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L89-L92

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

theorem GallaiEdmonds.cc_eq_of_closed (hW : W' ⊆ W) (hc : Closed G W W') (hx : x ∈ W') :
    cc G W' x = cc G W x := by sorry
