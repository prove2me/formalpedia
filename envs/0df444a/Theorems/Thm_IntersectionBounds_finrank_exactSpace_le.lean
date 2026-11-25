-- Prove2me | Theorems.Thm_IntersectionBounds_finrank_exactSpace_le
-- name    : IntersectionBounds.finrank_exactSpace_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:49:43.610316+00:00
-- url     : https://prove2.me/theorems/3f78c304-a882-5f9d-b46a-f19e725480d2
-- title:
--   Intersection Bounds: finrank exact Space le
-- statement:
--   The Intersection Bounds construction uses the finrank exact Space le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/UniformSpace.lean#L73-L95
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/UniformSpace.lean#L73-L95

module
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Definitions.Def_IntersectionBounds_Definitions
public import Definitions.Def_IntersectionBounds_UniformSpace
set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V] {K : Type v} [Field K]
variable (F : Finset (Finset V))

theorem IntersectionBounds.finrank_exactSpace_le (s : ℕ) :
    Module.finrank K (exactSpace F s : Submodule K (F → K)) ≤ (Fintype.card V).choose s := by sorry
