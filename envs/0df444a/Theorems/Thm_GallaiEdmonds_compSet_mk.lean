-- Prove2me | Theorems.Thm_GallaiEdmonds_compSet_mk
-- name    : GallaiEdmonds.compSet_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:27.432461+00:00
-- url     : https://prove2.me/theorems/bdc21168-dc56-453c-8cc2-52fc18a9fbbb
-- title:
--   Gallai Edmonds: comp Set mk
-- statement:
--   The Gallai Edmonds construction uses the comp Set mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L113-L122
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L113-L122

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

theorem GallaiEdmonds.compSet_mk [Finite V] {U : Set V} (hU : IsMinBarrier G U) (x : V) (hx : x ∈ setD G) :
    compSet G ((G.induce (setD G)).connectedComponentMk ⟨x, hx⟩) = cc G Uᶜ x := by sorry
