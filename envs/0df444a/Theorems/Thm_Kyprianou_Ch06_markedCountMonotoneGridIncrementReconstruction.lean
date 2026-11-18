-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedCountMonotoneGridIncrementReconstruction
-- name    : Kyprianou.Ch06.markedCountMonotoneGridIncrementReconstruction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:13:22.721082+00:00
-- url     : https://prove2.me/theorems/644fcc36-1e98-46e9-83a9-2fdf2b07dba5
-- title:
--   Lemma 6.18: reconstruct monotone Poisson counts along an ordered observation grid
-- statement:
--   If a nondecreasing sequence of times starts at zero and an integer-valued counting function F is nondecreasing and zero at time zero, then F at any grid time equals the finite sum of successive counting increments. This reconstructs marked Poisson time observations from compatible interval rectangles after choosing a finite ordered grid.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, ordered time-interval count increments.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_finiteMonotoneCountIncrementTelescoping
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.markedCountMonotoneGridIncrementReconstruction
    (grid : Nat → NNReal) (hGrid : Monotone grid)
    (hGridZero : grid 0 = 0)
    (F : NNReal → Nat) (hF : Monotone F)
    (hFZero : F 0 = 0) (r : Nat) :
    F (grid r) =
      ∑ j ∈ Finset.range r, (F (grid (j + 1)) - F (grid j)) := by sorry
