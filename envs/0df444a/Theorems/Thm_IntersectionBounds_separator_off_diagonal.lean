-- Prove2me | Theorems.Thm_IntersectionBounds_separator_off_diagonal
-- name    : IntersectionBounds.separator_off_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:46:07.641385+00:00
-- url     : https://prove2.me/theorems/8183f58e-4ff8-4e96-8cd1-c9ab93bf1ae9
-- title:
--   Intersection Bounds: separator off diagonal
-- statement:
--   The Intersection Bounds construction uses the separator off diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/Separation.lean#L26-L31
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/Separation.lean#L26-L31

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
open Classical

theorem IntersectionBounds.separator_off_diagonal (A B : F) (h : ((A.val ∩ B.val).card : K) ∈ L) :
    separator F L A.val B = 0 := by sorry
