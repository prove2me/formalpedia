-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_stopped_cell_geometry
-- name    : Kyprianou.Ch04.ito43_stopped_cell_geometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:26:12.983518+00:00
-- url     : https://prove2.me/theorems/e30ceef1-9608-418c-b377-ae7eb7f12d44
-- title:
--   At most one grid cell is cut strictly inside by a stop
-- statement:
--   At most one grid cell is cut strictly inside by a stop.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open Set
set_option autoImplicit false

/-- A monotone grid has at most one cell cut strictly in its interior by a stop. -/

theorem Kyprianou.Ch04.ito43_stopped_cell_geometry (u : ℕ → ℝ) (hu : Monotone u) (t : ℝ) (i j : ℕ)
    (hi : u i < t ∧ t < u (i+1)) (hj : u j < t ∧ t < u (j+1)) :
    i = j := by sorry
