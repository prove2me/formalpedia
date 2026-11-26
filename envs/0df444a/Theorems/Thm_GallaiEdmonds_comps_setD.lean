-- Prove2me | Theorems.Thm_GallaiEdmonds_comps_setD
-- name    : GallaiEdmonds.comps_setD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:52.038856+00:00
-- url     : https://prove2.me/theorems/482a2197-781c-4f88-bfc8-a7f0583b3c00
-- title:
--   Gallai Edmonds: comps set D
-- statement:
--   The Gallai Edmonds construction uses the comps set D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L133-L144
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L133-L144

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

theorem GallaiEdmonds.comps_setD [Finite V] {U : Set V} (hU : IsMinBarrier G U) :
    comps G (setD G) = oddComps G Uᶜ := by sorry
