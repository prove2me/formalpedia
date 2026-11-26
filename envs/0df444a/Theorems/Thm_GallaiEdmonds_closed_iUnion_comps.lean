-- Prove2me | Theorems.Thm_GallaiEdmonds_closed_iUnion_comps
-- name    : GallaiEdmonds.closed_iUnion_comps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:17.928628+00:00
-- url     : https://prove2.me/theorems/0ae07f42-6a01-57c8-9024-4a7e4b3df2cd
-- title:
--   Gallai Edmonds: closed i Union comps
-- statement:
--   The Gallai Edmonds construction uses the closed i Union comps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L162-L164
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L162-L164

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

theorem GallaiEdmonds.closed_iUnion_comps {Q : Set (Set V)} (hQ : Q ⊆ comps G W) : Closed G W (⋃₀ Q) := by sorry
