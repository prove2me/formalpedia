-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_stoppedStrictPathIffRationalMarginAE
-- name    : Kyprianou.Ch08.StageB.stoppedStrictPathIffRationalMarginAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:32:24.649889+00:00
-- url     : https://prove2.me/theorems/582debc4-35af-4163-8545-1b9244cd563d
-- title:
--   Lemma 8.2: strict original pre-stop path event equals countable rational uniform-gap certificate under compact upper semicontinuity
-- statement:
--   Assuming path right-continuity and upper semicontinuity on every finite compact interval almost surely, a path is strictly below a height at every point before a possibly infinite stop exactly when, for every nonnegative rational time cutoff before the stop, all rational observations up to that cutoff are uniformly below the height by some reciprocal-integer margin. Forward direction follows from maximum attainment of an upper semicontinuous function on each compact cutoff. Reverse direction uses rational time cutoffs and rational approximation from the right. No atom-free assumption or finite stopping-time hypothesis is used.
-- source:
--   Kyprianou Chapter 8 Lemma 8.2 strict excursion heights, with pinned Mathlib compact upper semicontinuity and rational density. Proof burden for generic stoppedStrictPathEventNullMeasurable.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.stoppedStrictPathIffRationalMarginAE
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (h : ℝ)
    (hpath : ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0,
        ContinuousWithinAt (fun s => f s ω) (Set.Ici t) t) ∧
      (∀ z : ℝ≥0,
        UpperSemicontinuousOn (fun s => f s ω) (Set.Icc 0 z))) :
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0,
        (t : WithTop ℝ≥0) < T ω → f t ω < h) ↔
      (∀ q : ℚ, 0 ≤ q →
          ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω →
          ∃ n : ℕ,
            ∀ r : ℚ, 0 ≤ r → r ≤ q →
              f (r : ℝ).toNNReal ω <
                h - 1 / (((n + 1 : ℕ) : ℝ))) := by
  sorry
