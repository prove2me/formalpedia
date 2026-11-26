-- Prove2me | Theorems.Thm_GallaiEdmonds_oddPart_closed
-- name    : GallaiEdmonds.oddPart_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:11.956566+00:00
-- url     : https://prove2.me/theorems/a95df3ff-ccda-593f-add2-214e59c68159
-- title:
--   Gallai Edmonds: odd Part closed
-- statement:
--   The Gallai Edmonds construction uses the odd Part closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L63-L66
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L63-L66

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

theorem GallaiEdmonds.oddPart_closed (U : Set V) : Closed G Uᶜ (oddPart G U) := by sorry
