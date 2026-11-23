-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationPhysicalRestartShift
-- name    : Kyprianou.Ch01.reciprocalOccupationPhysicalRestartShift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:02:38.516084+00:00
-- url     : https://prove2.me/theorems/f72cb359-febc-4afd-b2a9-0c5dc3662921
-- title:
--   Reciprocal occupation integrates a positive prefix and shifted tail
-- statement:
--   For any physical time u not earlier than A, the reciprocal-occupation integral of the path with constant positive prefix y equals A/y plus the reciprocal-occupation integral of the translated tail path. The zero-measure joining time is harmless. This exact clock identity is the principal integration step for the inverse Lamperti first-jump clock shift.
-- source:
--   Kyprianou (2006), Section 1.3.4; deterministic reverse Lamperti clock translation at the first marked arrival.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reciprocalOccupationPhysicalRestartShift
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω)
    (u : ℝ≥0) (hu : A ≤ (u : ℝ)) :
    reciprocalOccupation X u ω =
      ENNReal.ofReal (A / (y : ℝ)) +
        reciprocalOccupation Y (Real.toNNReal ((u : ℝ) - A)) ω := by
  sorry
