-- Prove2me | Theorems.Thm_GallaiEdmondsTheorem_two_mul_card_add
-- name    : GallaiEdmondsTheorem.two_mul_card_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:39.191379+00:00
-- url     : https://prove2.me/theorems/d5c5f997-ed9b-4a09-9700-0511ef2b6468
-- title:
--   Gallai Edmonds Theorem: two mul card add
-- statement:
--   **The Gallai–Edmonds formula.** For every maximum matching `M`,
--   `2|M| + c(D(G)) = |V| + |A(G)|`.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L98-L101
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L98-L101

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_GallaiEdmonds_two_mul_card_add

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmondsTheorem
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)

theorem GallaiEdmondsTheorem.two_mul_card_add [Finite V] {M : G.Subgraph} (hM : IsMaximumMatching G M) :
    2 * M.edgeSet.ncard + Nat.card (G.induce (setD G)).ConnectedComponent =
      Nat.card V + (setA G).ncard := by sorry
