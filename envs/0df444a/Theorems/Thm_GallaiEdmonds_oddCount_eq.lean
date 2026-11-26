-- Prove2me | Theorems.Thm_GallaiEdmonds_oddCount_eq
-- name    : GallaiEdmonds.oddCount_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:38.112739+00:00
-- url     : https://prove2.me/theorems/b88cafdd-29f2-4953-98da-55c0044640d0
-- title:
--   Gallai Edmonds: odd Count eq
-- statement:
--   The Gallai Edmonds construction uses the odd Count eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L246-L256
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L246-L256

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

theorem GallaiEdmonds.oddCount_eq [Finite V] (H : SimpleGraph V) (U : Set V) :
    BergeMatching.oddCount H U = oddC H Uᶜ := by sorry
