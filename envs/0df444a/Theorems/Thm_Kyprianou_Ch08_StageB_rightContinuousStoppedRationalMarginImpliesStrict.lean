-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_rightContinuousStoppedRationalMarginImpliesStrict
-- name    : Kyprianou.Ch08.StageB.rightContinuousStoppedRationalMarginImpliesStrict
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T11:45:48.308574+00:00
-- url     : https://prove2.me/theorems/b39a75fc-d0fe-48fc-af01-1d535ea157d3
-- title:
--   Lemma 8.2: right-continuity turns rational stopped uniform-height margins into the genuine all-times strict pre-stop bound
-- statement:
--   Let a real path be right-continuous at every nonnegative real time, and let the possibly infinite stop be any extended nonnegative time. Suppose that every nonnegative rational cutoff strictly before that stop admits a common positive reciprocal-integer gap below a fixed height across all rational observations up to the cutoff. Then at every real time strictly before the stop the actual path value lies strictly below the height. Use density of rational cutoffs between a real time and a later stop, and right-continuity to pass the rational gap to that real time. This proves the direction where replacing an exact-height contact by strict rational observations would otherwise lose an atom.
-- source:
--   Analytic right-continuity/rational-density child of Kyprianou.Ch08.StageB.stoppedStrictPathIffRationalMarginAE 582debc4-35af-4163-8545-1b9244cd563d in connected Chapter 8 Lemma 8.2.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.rightContinuousStoppedRationalMarginImpliesStrict
    (f : ℝ≥0 → ℝ) (T : WithTop ℝ≥0) (h : ℝ)
    (hright : ∀ t : ℝ≥0,
      ContinuousWithinAt f (Set.Ici t) t)
    (hmargin : ∀ q : ℚ, 0 ≤ q →
      ((q : ℝ).toNNReal : WithTop ℝ≥0) < T →
      ∃ n : ℕ, ∀ r : ℚ, 0 ≤ r → r ≤ q →
        f (r : ℝ).toNNReal <
          h - 1 / (((n + 1 : ℕ) : ℝ))) :
    ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < T → f t < h := by
  sorry
