-- Prove2me | Theorems.Thm_GallaiEdmonds_IsBarrier_eq
-- name    : GallaiEdmonds.IsBarrier.eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:01:26.06182+00:00
-- url     : https://prove2.me/theorems/2bc674cc-a6a7-402a-b1db-a2e757df88a2
-- title:
--   Is Barrier: eq
-- statement:
--   The Is Barrier construction uses the eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEBarrier.lean#L47-L54
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEBarrier.lean#L47-L54

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}

theorem GallaiEdmonds.IsBarrier.eq [Finite V] {U : Set V} (hU : IsBarrier G U) {M : G.Subgraph}
    (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard := by sorry
