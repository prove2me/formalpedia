-- Prove2me | Theorems.Thm_GallaiEdmonds_mem_setC_iff
-- name    : GallaiEdmonds.mem_setC_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:19.991636+00:00
-- url     : https://prove2.me/theorems/c5756ea6-3fd7-4c75-9a9b-4549734704ea
-- title:
--   Gallai Edmonds: mem set C iff
-- statement:
--   The Gallai Edmonds construction uses the mem set C iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L107-L111
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L107-L111

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

theorem GallaiEdmonds.mem_setC_iff [Finite V] {U : Set V} (hU : IsMinBarrier G U) (w : V) :
    w ∈ setC G ↔ w ∉ U ∧ Even (cc G Uᶜ w).ncard := by sorry
