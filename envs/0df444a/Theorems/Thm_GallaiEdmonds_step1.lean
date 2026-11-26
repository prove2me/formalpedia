-- Prove2me | Theorems.Thm_GallaiEdmonds_step1
-- name    : GallaiEdmonds.step1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:01:21.069694+00:00
-- url     : https://prove2.me/theorems/18ccb08b-d66c-546e-9004-21ab9e995a21
-- title:
--   Gallai Edmonds: step1
-- statement:
--   Equality analysis of the Tutte–Berge inequality.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L127-L238
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean#L127-L238

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}

theorem GallaiEdmonds.step1 [Finite V] {M : G.Subgraph} (hM : M.IsMatching) {U : Set V}
    (hEq : M.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard) :
    (∀ u ∈ U, ∃ x, M.Adj u x ∧ x ∉ U ∧ Odd (cc G Uᶜ x).ncard) ∧
    (∀ u ∈ U, ∀ u' ∈ U, ∀ x x', u ≠ u' → M.Adj u x → M.Adj u' x' →
      cc G Uᶜ x ≠ cc G Uᶜ x') ∧
    (∀ K ∈ oddComps G Uᶜ, ∀ y ∈ K, ∀ z ∈ K, y ≠ z →
      (∃ w ∈ K, M.Adj y w) ∨ (∃ w ∈ K, M.Adj z w)) ∧
    (∀ y, y ∉ U → Even (cc G Uᶜ y).ncard → ∃ w ∈ cc G Uᶜ y, M.Adj y w) := by sorry
