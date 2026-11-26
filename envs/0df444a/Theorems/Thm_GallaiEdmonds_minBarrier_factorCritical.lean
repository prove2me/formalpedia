-- Prove2me | Theorems.Thm_GallaiEdmonds_minBarrier_factorCritical
-- name    : GallaiEdmonds.minBarrier_factorCritical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:02:03.135433+00:00
-- url     : https://prove2.me/theorems/d9bd1181-90b9-4095-a46a-3a150f14caab
-- title:
--   Gallai Edmonds: min Barrier factor Critical
-- statement:
--   The odd components of `G − U` are factor-critical, for a minimal barrier `U`.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEBarrier.lean#L70-L144
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEBarrier.lean#L70-L144

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

theorem GallaiEdmonds.minBarrier_factorCritical [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    {M : G.Subgraph} (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard)
    {K : Set V} (hK : K ∈ oddComps G Uᶜ) {v : V} (hv : v ∈ K) :
    ∃ P : G.Subgraph, P.IsMatching ∧ P.verts = K \ {v} := by sorry
