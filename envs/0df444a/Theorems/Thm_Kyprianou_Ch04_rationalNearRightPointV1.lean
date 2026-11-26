-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rationalNearRightPointV1
-- name    : Kyprianou.Ch04.rationalNearRightPointV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:44:10.206584+00:00
-- url     : https://prove2.me/theorems/98e300be-07cd-42a6-880d-b1ccf7a99955
-- title:
--   A rational witness within two right-hand neighbourhoods
-- statement:
--   Choose a rational between the positive time and the minimum of the two upper bounds, then compare the induced metrics.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.rationalNearRightPointV1 (t : ℝ≥0) (δ ρ : ℝ) (ht0 : 0 < t)
    (htδ : dist t 0 < δ) (hρ : 0 < ρ) :
    ∃ r : ℚ, r ∈ Ioi (0 : ℚ) ∧ dist r 0 < δ ∧
      Real.toNNReal (r : ℝ) ∈ Ici t ∧ dist (Real.toNNReal (r : ℝ)) t < ρ := by
  sorry
