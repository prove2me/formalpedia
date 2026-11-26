-- Prove2me | Theorems.Thm_GallaiEdmonds_setD_eq
-- name    : GallaiEdmonds.setD_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:04:56.540819+00:00
-- url     : https://prove2.me/theorems/3378c3ee-cc8c-55f1-ab64-f51e059590ac
-- title:
--   Gallai Edmonds: set D eq
-- statement:
--   The Gallai Edmonds construction uses the set D eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L74-L89
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L74-L89

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)

theorem GallaiEdmonds.setD_eq [Finite V] {U : Set V} (hU : IsMinBarrier G U) : setD G = oddPart G U := by sorry
