-- Prove2me | Theorems.Thm_IntersectionBounds_sharp_example
-- name    : IntersectionBounds.sharp_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:26:10.877159+00:00
-- url     : https://prove2.me/theorems/501fe357-5562-49fb-9e29-5de379eb9762
-- title:
--   Intersection Bounds: sharp example
-- statement:
--   Every s-subset is an equality example, with intersection sizes in {0,...,s-1}.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L99-L109
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L99-L109

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

theorem IntersectionBounds.sharp_example (s : ℕ) :
    let F := (univ : Finset V).powersetCard s
    Uniform F s ∧ IntersectionsIn F (range s) ∧ F.card = (Fintype.card V).choose s := by sorry
