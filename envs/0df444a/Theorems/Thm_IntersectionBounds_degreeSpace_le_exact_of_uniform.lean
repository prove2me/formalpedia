-- Prove2me | Theorems.Thm_IntersectionBounds_degreeSpace_le_exact_of_uniform
-- name    : IntersectionBounds.degreeSpace_le_exact_of_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:49:27.778238+00:00
-- url     : https://prove2.me/theorems/b50a6171-eeef-5fcd-bac4-ea2910be6238
-- title:
--   Intersection Bounds: degree Space le exact of uniform
-- statement:
--   The Intersection Bounds construction uses the degree Space le exact of uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/UniformSpace.lean#L66-L71
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/UniformSpace.lean#L66-L71

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

theorem IntersectionBounds.degreeSpace_le_exact_of_uniform [CharZero K] (k s : ℕ)
    (huni : Uniform F k) (hs : s ≤ k) :
    degreeSpace F s ≤ (exactSpace F s : Submodule K (F → K)) := by sorry
