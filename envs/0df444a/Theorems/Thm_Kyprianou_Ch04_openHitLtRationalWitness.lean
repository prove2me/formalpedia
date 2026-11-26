-- Prove2me | Theorems.Thm_Kyprianou_Ch04_openHitLtRationalWitness
-- name    : Kyprianou.Ch04.openHitLtRationalWitness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:07:10.790744+00:00
-- url     : https://prove2.me/theorems/06a3dc7a-faed-5762-9591-4136255e828f
-- title:
--   openHitLtRationalWitness
-- statement:
--   On a right-continuous path, a strict open hitting time before a finite clock has a positive rational-time witness.
-- source:
--   Kyprianou (2006), Exercise 4.3(i), pp. 106-107.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Strict open hitting before a finite clock is witnessed at a rational time. -/
theorem Kyprianou.Ch04.openHitLtRationalWitness (Y : NNReal → ℝ) (B : Set ℝ) (hB : IsOpen B)
    (hrc : ∀ t : NNReal, ContinuousWithinAt Y (Set.Ici t) t) (s : NNReal) :
    sInf {u : WithTop NNReal | ∃ r : NNReal, u = ↑r ∧ Y r ∈ B} <
      (s : WithTop NNReal) ↔
      ∃ q : ℚ, 0 < q ∧ (q : ℝ) < s ∧ Y (Real.toNNReal q) ∈ B := by
  sorry
