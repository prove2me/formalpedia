-- Prove2me | Theorems.Thm_IntersectionBounds_intersection_lt_of_uniform
-- name    : IntersectionBounds.intersection_lt_of_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:49:40.219549+00:00
-- url     : https://prove2.me/theorems/9ac7ef10-0a7e-5612-bac8-bee26f4f4b71
-- title:
--   Intersection Bounds: intersection lt of uniform
-- statement:
--   The Intersection Bounds construction uses the intersection lt of uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L64-L73
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L64-L73

module
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Mathlib.Data.Rat.Cast.CharZero
public import Definitions.Def_IntersectionBounds_RayChaudhuriWilson
set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V]
open Classical
omit [Fintype V]

theorem IntersectionBounds.intersection_lt_of_uniform (F : Finset (Finset V)) (k : ℕ)
    (huni : Uniform F k) (A B : Finset V) (hA : A ∈ F) (hB : B ∈ F) (hne : A ≠ B) :
    (A ∩ B).card < k := by sorry
