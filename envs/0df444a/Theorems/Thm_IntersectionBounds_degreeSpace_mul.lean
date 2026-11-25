-- Prove2me | Theorems.Thm_IntersectionBounds_degreeSpace_mul
-- name    : IntersectionBounds.degreeSpace_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:41:58.728151+00:00
-- url     : https://prove2.me/theorems/cad5f961-8e4c-4cd4-8112-d522d105edd7
-- title:
--   Intersection Bounds: degree Space mul
-- statement:
--   The Intersection Bounds construction uses the degree Space mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/EvaluationSpace.lean#L48-L69
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/EvaluationSpace.lean#L48-L69

module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Definitions.Def_IntersectionBounds_EvaluationSpace
set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V))

theorem IntersectionBounds.degreeSpace_mul {a b : ℕ} {f g : F → K}
    (hf : f ∈ degreeSpace F a) (hg : g ∈ degreeSpace F b) :
    f * g ∈ degreeSpace F (a + b) := by sorry
