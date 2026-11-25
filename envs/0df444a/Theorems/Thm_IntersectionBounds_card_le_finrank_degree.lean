-- Prove2me | Theorems.Thm_IntersectionBounds_card_le_finrank_degree
-- name    : IntersectionBounds.card_le_finrank_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:46:03.70602+00:00
-- url     : https://prove2.me/theorems/ce4a0ebc-8a63-5470-9f1f-02a3d65e0612
-- title:
--   Intersection Bounds: card le finrank degree
-- statement:
--   The Intersection Bounds construction uses the card le finrank degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/Separation.lean#L57-L71
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/Separation.lean#L57-L71

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

theorem IntersectionBounds.card_le_finrank_degree
    (hself : ∀ A ∈ F, (A.card : K) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : K) ∈ L) :
    F.card ≤ Module.finrank K (degreeSpace (K := K) F L.card) := by sorry
