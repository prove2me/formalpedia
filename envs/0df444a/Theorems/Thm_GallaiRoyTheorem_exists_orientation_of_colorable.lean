-- Prove2me | Theorems.Thm_GallaiRoyTheorem_exists_orientation_of_colorable
-- name    : GallaiRoyTheorem.exists_orientation_of_colorable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:22:50.576975+00:00
-- url     : https://prove2.me/theorems/058e49f1-9de4-43c2-a624-3fb2cb0cb0d8
-- title:
--   Gallai Roy Theorem: exists orientation of colorable
-- statement:
--   Conversely, a `k`-colourable graph has an orientation without directed paths on more than `k`
--   vertices (orient every edge towards the larger colour).
--
--   Source: https://github.com/jtraverso/gallai-roy/blob/e737218bf80c3d3684d670f5f8aa9a8257e1a52f/Solution.lean#L47-L50
-- source:
--   https://github.com/jtraverso/gallai-roy/blob/e737218bf80c3d3684d670f5f8aa9a8257e1a52f/Solution.lean#L47-L50

module
public import Mathlib
public import Definitions.Def_GallaiRoyLib_GallaiRoy
public import Definitions.Def_GallaiRoy_Solution
public import Theorems.Thm_GallaiRoy_exists_orientation_of_colorable

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiRoyTheorem
variable {V : Type*}

theorem GallaiRoyTheorem.exists_orientation_of_colorable (G : SimpleGraph V) (k : ℕ) (h : G.Colorable k) :
    ∃ o : V → V → Prop, IsOrientation G o ∧
      ∀ (m : ℕ) (f : Fin m → V), IsDirectedPath o f → m ≤ k := by sorry
