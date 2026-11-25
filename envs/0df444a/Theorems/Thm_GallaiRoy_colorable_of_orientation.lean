-- Prove2me | Theorems.Thm_GallaiRoy_colorable_of_orientation
-- name    : GallaiRoy.colorable_of_orientation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:15:38.183081+00:00
-- url     : https://prove2.me/theorems/1eac5825-bef6-4f6e-9f45-cfc1f1a6dc47
-- title:
--   Gallai Roy: colorable of orientation
-- statement:
--   **Gallai–Hasse–Roy–Vitaver.** If an orientation of a finite graph has no directed path on more
--   than `k` vertices, the graph is `k`-colourable.
--
--   Source: https://github.com/jtraverso/gallai-roy/blob/e737218bf80c3d3684d670f5f8aa9a8257e1a52f/GallaiRoyLib/GallaiRoy.lean#L94-L147
-- source:
--   https://github.com/jtraverso/gallai-roy/blob/e737218bf80c3d3684d670f5f8aa9a8257e1a52f/GallaiRoyLib/GallaiRoy.lean#L94-L147

module
public import Mathlib
public import Definitions.Def_GallaiRoyLib_GallaiRoy
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiRoy
variable {V : Type*}

theorem GallaiRoy.colorable_of_orientation [Finite V] (G : SimpleGraph V) (o : V → V → Prop)
    (ho : IsOrientation G o) (k : ℕ)
    (hk : ∀ (m : ℕ) (f : Fin m → V), IsDirectedPath o f → m ≤ k) : G.Colorable k := by sorry
