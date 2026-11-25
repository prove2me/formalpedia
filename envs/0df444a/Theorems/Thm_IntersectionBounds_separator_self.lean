-- Prove2me | Theorems.Thm_IntersectionBounds_separator_self
-- name    : IntersectionBounds.separator_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:46:05.889578+00:00
-- url     : https://prove2.me/theorems/ac459635-cde0-4c47-85af-3506e2c726d0
-- title:
--   Intersection Bounds: separator self
-- statement:
--   The Intersection Bounds construction uses the separator self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/Separation.lean#L20-L23
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/Separation.lean#L20-L23

module
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Definitions.Def_IntersectionBounds_Separation
set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V)) (L : Finset K)

theorem IntersectionBounds.separator_self (A : F) :
    separator F L A.val A = ∏ l ∈ L, ((A.val.card : K) - l) := by sorry
