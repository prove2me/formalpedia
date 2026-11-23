-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiShiftedStoppedInverseClock
-- name    : Kyprianou.Ch01.reverseLampertiShiftedStoppedInverseClock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:08:54.830891+00:00
-- url     : https://prove2.me/theorems/0de88083-a67c-4b90-9805-533ccf713df7
-- title:
--   Shift of the stopped inverse reciprocal-occupation clock
-- statement:
--   The first-negative-passage-stopped right-inverse of the occupation clock of a path with constant positive prefix of length A agrees with A plus the corresponding stopped right-inverse of its shifted tail at residual branching time. Assume the shifted tail is nonnegative at time zero to ensure the first-negative-passage endpoint translates correctly. This is the actual clock-identity premise that reduces the corrected reverse Lamperti population equality to a path substitution. Proof obligations include decomposition of the Lebesgue occupation integral over the prefix, inversion of the resulting monotone clocks and translation of the sInf negative-passage set.
-- source:
--   Kyprianou (2006), Section 1.3.4, stopped inverse occupation clocks under the first marked arrival and corrected nonnegative tail start.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiShiftedStoppedInverseClock
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    min (inverseReciprocalOccupation X t ω) (firstNegativePassage X ω) =
      (((Real.toNNReal A : ℝ≥0) : WithTop ℝ≥0) +
        min
          (inverseReciprocalOccupation Y
            (Real.toNNReal ((t : ℝ) - A / (y : ℝ))) ω)
          (firstNegativePassage Y ω)) := by
  sorry
