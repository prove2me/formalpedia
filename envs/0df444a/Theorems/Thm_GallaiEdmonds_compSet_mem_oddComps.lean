-- Prove2me | Theorems.Thm_GallaiEdmonds_compSet_mem_oddComps
-- name    : GallaiEdmonds.compSet_mem_oddComps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:18.496853+00:00
-- url     : https://prove2.me/theorems/c777ab53-83c6-5272-9589-079c944aeaba
-- title:
--   Gallai Edmonds: comp Set mem odd Comps
-- statement:
--   The Gallai Edmonds construction uses the comp Set mem odd Comps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L124-L131
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L124-L131

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

theorem GallaiEdmonds.compSet_mem_oddComps [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    (c : (G.induce (setD G)).ConnectedComponent) : compSet G c ∈ oddComps G Uᶜ := by sorry
