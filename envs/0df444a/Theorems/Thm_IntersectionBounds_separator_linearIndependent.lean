-- Prove2me | Theorems.Thm_IntersectionBounds_separator_linearIndependent
-- name    : IntersectionBounds.separator_linearIndependent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T12:46:10.999177+00:00
-- url     : https://prove2.me/theorems/a080b34b-898a-471d-9237-16f7b4651f3a
-- title:
--   Intersection Bounds: separator linear Independent
-- statement:
--   The Intersection Bounds construction uses the separator linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/Separation.lean#L34-L54
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/Separation.lean#L34-L54

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

theorem IntersectionBounds.separator_linearIndependent
    (hself : ∀ A ∈ F, (A.card : K) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : K) ∈ L) :
    LinearIndependent K (fun A : F => separator F L A.val) := by sorry
