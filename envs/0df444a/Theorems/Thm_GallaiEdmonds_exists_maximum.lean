-- Prove2me | Theorems.Thm_GallaiEdmonds_exists_maximum
-- name    : GallaiEdmonds.exists_maximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:17.749388+00:00
-- url     : https://prove2.me/theorems/2947d5f0-31ac-4a08-9d3d-8a5547a4dc7a
-- title:
--   Gallai Edmonds: exists maximum
-- statement:
--   The Gallai Edmonds construction uses the exists maximum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L70-L72
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean#L70-L72

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

theorem GallaiEdmonds.exists_maximum [Finite V] : ∃ M : G.Subgraph, IsMaximumMatching G M := by sorry
