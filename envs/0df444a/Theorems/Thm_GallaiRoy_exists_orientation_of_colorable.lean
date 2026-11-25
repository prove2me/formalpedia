-- Prove2me | Theorems.Thm_GallaiRoy_exists_orientation_of_colorable
-- name    : GallaiRoy.exists_orientation_of_colorable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:15:58.128164+00:00
-- url     : https://prove2.me/theorems/9cf35d27-c948-4cc8-9687-d3d2b4373718
-- title:
--   Gallai Roy: exists orientation of colorable
-- statement:
--   Conversely, a `k`-colourable graph has an orientation without directed paths on more than `k`
--   vertices (orient every edge towards the larger colour).
--
--   Source: https://github.com/jtraverso/gallai-roy/blob/e737218bf80c3d3684d670f5f8aa9a8257e1a52f/GallaiRoyLib/GallaiRoy.lean#L151-L167
-- source:
--   https://github.com/jtraverso/gallai-roy/blob/e737218bf80c3d3684d670f5f8aa9a8257e1a52f/GallaiRoyLib/GallaiRoy.lean#L151-L167

module
public import Mathlib
public import Definitions.Def_GallaiRoyLib_GallaiRoy
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiRoy
variable {V : Type*}

theorem GallaiRoy.exists_orientation_of_colorable (G : SimpleGraph V) (k : ℕ) (h : G.Colorable k) :
    ∃ o : V → V → Prop, IsOrientation G o ∧
      ∀ (m : ℕ) (f : Fin m → V), IsDirectedPath o f → m ≤ k := by sorry
