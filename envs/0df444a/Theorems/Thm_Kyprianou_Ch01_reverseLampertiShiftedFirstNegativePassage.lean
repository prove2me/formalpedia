-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiShiftedFirstNegativePassage
-- name    : Kyprianou.Ch01.reverseLampertiShiftedFirstNegativePassage
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:15:08.199512+00:00
-- url     : https://prove2.me/theorems/fd88b739-8077-4a83-907a-d71b41a19e9f
-- title:
--   First negative passage shifts across a positive constant prefix
-- statement:
--   Because X is strictly positive before A and Y is nonnegative at time zero, the strictly positive-time negative-passage set of X is the translated strictly positive-time negative-passage set of Y. Apply translation invariance of the infimum of this set, preserving top for the empty set.
-- source:
--   Kyprianou (2006) Section 1.3.4, exact deterministic first-arrival clock shift; source-bound sublemma of the corrected stopped-clock identity 0de88083-a67c-4b90-9805-533ccf713df7.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiShiftedFirstNegativePassage
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    firstNegativePassage X ω =
      (((Real.toNNReal A : ℝ≥0) : WithTop ℝ≥0) +
        firstNegativePassage Y ω) := by
  sorry
