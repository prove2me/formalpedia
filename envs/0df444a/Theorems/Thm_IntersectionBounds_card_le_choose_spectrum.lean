-- Prove2me | Theorems.Thm_IntersectionBounds_card_le_choose_spectrum
-- name    : IntersectionBounds.card_le_choose_spectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:53:41.916146+00:00
-- url     : https://prove2.me/theorems/5be9c088-562e-5df7-847e-c7a078dd2781
-- title:
--   Intersection Bounds: card le choose spectrum
-- statement:
--   A canonical form using exactly the intersection sizes that actually occur.
--
--   Source: https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L76-L85
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean#L76-L85

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

theorem IntersectionBounds.card_le_choose_spectrum (F : Finset (Finset V)) (k : ℕ) (huni : Uniform F k) :
    F.card ≤ (Fintype.card V).choose (intersectionSpectrum F).card := by sorry
