-- Prove2me | Theorems.Thm_IntersectionBounds_indicator_mem_exact_of_uniform
-- name    : IntersectionBounds.indicator_mem_exact_of_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:46:38.14608+00:00
-- url     : https://prove2.me/theorems/4979019f-90f2-44de-aaa1-47981a41fd8d
-- title:
--   Intersection Bounds: indicator mem exact of uniform
-- statement:
--   The Intersection Bounds construction uses the indicator mem exact of uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/UniformSpace.lean#L38-L64
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/UniformSpace.lean#L38-L64

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

theorem IntersectionBounds.indicator_mem_exact_of_uniform [CharZero K] (k s : ℕ)
    (huni : Uniform F k) (hs : s ≤ k) (T : Finset V) (hT : T.card ≤ s) :
    (indicator F T : F → K) ∈ exactSpace F s := by sorry
