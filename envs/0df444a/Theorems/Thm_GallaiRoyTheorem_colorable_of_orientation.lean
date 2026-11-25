-- Prove2me | Theorems.Thm_GallaiRoyTheorem_colorable_of_orientation
-- name    : GallaiRoyTheorem.colorable_of_orientation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:21:06.905752+00:00
-- url     : https://prove2.me/theorems/40096471-aca0-4222-96e2-f9d1ce0159e8
-- title:
--   Gallai Roy Theorem: colorable of orientation
-- statement:
--   **Gallai–Hasse–Roy–Vitaver.** If an orientation of a finite graph has no directed path on more
--   than `k` vertices, the graph is `k`-colourable.
--
--   Source: https://github.com/jtraverso/gallai-roy/blob/e737218bf80c3d3684d670f5f8aa9a8257e1a52f/Solution.lean#L40-L43
-- source:
--   https://github.com/jtraverso/gallai-roy/blob/e737218bf80c3d3684d670f5f8aa9a8257e1a52f/Solution.lean#L40-L43

module
public import Mathlib
public import Definitions.Def_GallaiRoyLib_GallaiRoy
public import Definitions.Def_GallaiRoy_Solution
public import Theorems.Thm_GallaiRoy_colorable_of_orientation

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiRoyTheorem
variable {V : Type*}

theorem GallaiRoyTheorem.colorable_of_orientation [Finite V] (G : SimpleGraph V) (o : V → V → Prop)
    (ho : IsOrientation G o) (k : ℕ)
    (hk : ∀ (m : ℕ) (f : Fin m → V), IsDirectedPath o f → m ≤ k) : G.Colorable k := by sorry
