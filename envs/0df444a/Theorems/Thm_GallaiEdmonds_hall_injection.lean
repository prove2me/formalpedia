-- Prove2me | Theorems.Thm_GallaiEdmonds_hall_injection
-- name    : GallaiEdmonds.hall_injection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:02:45.498483+00:00
-- url     : https://prove2.me/theorems/7fa9aa14-447f-5dbd-a617-3905108adc7e
-- title:
--   Gallai Edmonds: hall injection
-- statement:
--   Hall's theorem applied to `U` and the odd components other than that of `v`.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEConstruct.lean#L29-L68
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEConstruct.lean#L29-L68

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}

theorem GallaiEdmonds.hall_injection [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    {M : G.Subgraph} (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard)
    {v : V} (hv : v ∈ oddPart G U) :
    ∃ f : V → Set V,
      (∀ u ∈ U, f u ∈ oddComps G Uᶜ ∧ f u ≠ cc G Uᶜ v ∧ ∃ x ∈ f u, G.Adj u x) ∧
      Set.InjOn f U := by sorry
