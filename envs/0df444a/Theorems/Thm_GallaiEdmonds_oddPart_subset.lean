-- Prove2me | Theorems.Thm_GallaiEdmonds_oddPart_subset
-- name    : GallaiEdmonds.oddPart_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:18.988343+00:00
-- url     : https://prove2.me/theorems/a9ae61d1-5bab-5aeb-a2c1-709f9ec1d953
-- title:
--   Gallai Edmonds: odd Part subset
-- statement:
--   The Gallai Edmonds construction uses the odd Part subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L68-L68
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L68-L68

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

theorem GallaiEdmonds.oddPart_subset (U : Set V) : oddPart G U ⊆ Uᶜ := by sorry
