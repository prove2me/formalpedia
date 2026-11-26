-- Prove2me | Theorems.Thm_GallaiEdmonds_minBarrier_surplus
-- name    : GallaiEdmonds.minBarrier_surplus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:02:04.040807+00:00
-- url     : https://prove2.me/theorems/3dd331ae-d820-4e19-9a35-8476a041e3bf
-- title:
--   Gallai Edmonds: min Barrier surplus
-- statement:
--   Hall's condition with surplus: every `s ⊆ U` is adjacent to at least `|s|` odd components
--   other than the component of a given vertex `v` of an odd component.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEBarrier.lean#L148-L229
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEBarrier.lean#L148-L229

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

theorem GallaiEdmonds.minBarrier_surplus [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    {M : G.Subgraph} (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard)
    {v : V} (hv : v ∈ oddPart G U) {s : Set V} (hs : s ⊆ U) :
    s.ncard ≤
      {K | K ∈ oddComps G Uᶜ ∧ K ≠ cc G Uᶜ v ∧ ∃ u ∈ s, ∃ x ∈ K, G.Adj u x}.ncard := by sorry
