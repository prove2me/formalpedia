-- Prove2me | Theorems.Thm_GallaiEdmondsTheorem_maximumMatching_structure
-- name    : GallaiEdmondsTheorem.maximumMatching_structure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:19.647808+00:00
-- url     : https://prove2.me/theorems/f3fdd6cf-d403-5008-84c3-c7e5b1adad7f
-- title:
--   Gallai Edmonds Theorem: maximum Matching structure
-- statement:
--   The structure of every maximum matching.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L86-L94
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L86-L94

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_GallaiEdmonds_maximumMatching_structure

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmondsTheorem
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)

theorem GallaiEdmondsTheorem.maximumMatching_structure [Finite V] {M : G.Subgraph} (hM : IsMaximumMatching G M) :
    (∀ v ∈ setC G, ∃ w ∈ setC G, M.Adj v w) ∧
    (∀ a ∈ setA G, ∃ u ∈ setD G, M.Adj a u) ∧
    (∀ a ∈ setA G, ∀ a' ∈ setA G, ∀ u u' : ↥(setD G), a ≠ a' → M.Adj a u → M.Adj a' u' →
      (G.induce (setD G)).connectedComponentMk u ≠
        (G.induce (setD G)).connectedComponentMk u') ∧
    (∀ c : (G.induce (setD G)).ConnectedComponent, ∀ v ∈ compSet G c, ∀ w ∈ compSet G c,
      v ≠ w → (∃ x ∈ compSet G c, M.Adj v x) ∨ (∃ x ∈ compSet G c, M.Adj w x)) := by sorry
