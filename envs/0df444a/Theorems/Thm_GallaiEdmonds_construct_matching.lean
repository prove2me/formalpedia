-- Prove2me | Theorems.Thm_GallaiEdmonds_construct_matching
-- name    : GallaiEdmonds.construct_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:02:50.89728+00:00
-- url     : https://prove2.me/theorems/6c8f1123-4f0b-5b54-b8aa-0b3cdd752b5d
-- title:
--   Gallai Edmonds: construct matching
-- statement:
--   Assembling a matching from the pieces.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEConstruct.lean#L71-L209
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEConstruct.lean#L71-L209

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

theorem GallaiEdmonds.construct_matching [Finite V] {U : Set V} {v : V} (hv : v ∈ oddPart G U)
    {f : V → Set V}
    (hf : ∀ u ∈ U, f u ∈ oddComps G Uᶜ ∧ f u ≠ cc G Uᶜ v ∧ ∃ x ∈ f u, G.Adj u x)
    (hfinj : Set.InjOn f U)
    (hfc : ∀ K ∈ oddComps G Uᶜ, ∀ y ∈ K, ∃ P : G.Subgraph, P.IsMatching ∧ P.verts = K \ {y})
    (hev : ∀ K ∈ comps G Uᶜ, Even K.ncard → ∃ P : G.Subgraph, P.IsMatching ∧ P.verts = K) :
    ∃ M' : G.Subgraph, M'.IsMatching ∧ v ∉ M'.verts ∧
      M'.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard := by sorry
