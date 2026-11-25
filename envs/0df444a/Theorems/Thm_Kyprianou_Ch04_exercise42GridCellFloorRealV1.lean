-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42GridCellFloorRealV1
-- name    : Kyprianou.Ch04.exercise42GridCellFloorRealV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T17:32:49.604307+00:00
-- url     : https://prove2.me/theorems/c7e96d0c-9543-5b7c-8440-f9915ec42606
-- title:
--   Floor index of a uniform positive-real grid cell
-- statement:
--   A point in a left-closed, right-open uniform grid interval has floor index equal to the interval number.
-- source:
--   Deterministic uniform-grid lemma supporting Kyprianou (2006), Exercise 4.2.

import Mathlib
open Set
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42GridCellFloorRealV1
    (T : ℝ) (hT : 0 < T) (n i : ℕ) (s : ℝ)
    (hs : s ∈ Set.Ico (T * (i : ℝ) / ((n : ℝ) + 2))
      (T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2))) :
    ⌊(s / T) * ((n : ℝ) + 2)⌋₊ = i := by
  sorry
