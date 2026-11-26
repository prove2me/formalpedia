-- Prove2me | Theorems.Thm_GallaiEdmonds_comps_self
-- name    : GallaiEdmonds.comps_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:16.828462+00:00
-- url     : https://prove2.me/theorems/99549e25-8865-4629-8207-7801f46e6e6d
-- title:
--   Gallai Edmonds: comps self
-- statement:
--   The Gallai Edmonds construction uses the comps self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L140-L148
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L140-L148

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

theorem GallaiEdmonds.comps_self {K : Set V} (hK : K ∈ comps G W) : comps G K = {K} := by sorry
