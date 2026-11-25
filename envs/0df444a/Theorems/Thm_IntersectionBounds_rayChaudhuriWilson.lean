-- Prove2me | Theorems.Thm_IntersectionBounds_rayChaudhuriWilson
-- name    : IntersectionBounds.rayChaudhuriWilson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:49:34.846325+00:00
-- url     : https://prove2.me/theorems/20c38304-5e32-58fe-b81e-d59690a429b7
-- title:
--   Intersection Bounds: ray Chaudhuri Wilson
-- statement:
--   Ray-Chaudhuri–Wilson (1975), Theorem 3: the sharp bound for a uniform
--   family whose distinct intersections have sizes in L ⊆ {0, ..., k-1}.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L37-L60
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L37-L60

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

theorem IntersectionBounds.rayChaudhuriWilson (F : Finset (Finset V)) (L : Finset ℕ) (k : ℕ)
    (huni : Uniform F k) (hL : ∀ l ∈ L, l < k) (hinter : IntersectionsIn F L) :
    F.card ≤ (Fintype.card V).choose L.card := by sorry
