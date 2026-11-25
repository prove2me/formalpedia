-- Prove2me | Theorems.Thm_IntersectionBounds_uniform_fisher
-- name    : IntersectionBounds.uniform_fisher
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:53:51.266991+00:00
-- url     : https://prove2.me/theorems/3ab0470a-bdf5-5d6a-ac84-303475d9c1c5
-- title:
--   Intersection Bounds: uniform fisher
-- statement:
--   The one-intersection case is the uniform Fisher bound.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L89-L95
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L89-L95

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

theorem IntersectionBounds.uniform_fisher (F : Finset (Finset V)) (k l : ℕ)
    (huni : Uniform F k) (hl : l < k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card = l) :
    F.card ≤ Fintype.card V := by sorry
