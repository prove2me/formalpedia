-- Prove2me | Theorems.Thm_Kyprianou_Ch02_locallySummableTimeRepresentationActualJumpsV1
-- name    : Kyprianou.Ch02.locallySummableTimeRepresentationActualJumpsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:51:15.846951+00:00
-- url     : https://prove2.me/theorems/d8f240fa-0285-42ed-9125-0f9164d51912
-- title:
--   The actual jumps of a locally absolutely summable chronological series are its marks
-- statement:
--   On each compact horizon extend the marks by zero to a globally summable series. The existing real atomic left-limit theorem gives the strict-time cumulative sum as the left limit. Subtract it from the inclusive-time sum, leaving exactly the mark at t.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12; canonical finite first moment model and equality of real Levy path laws.

import Mathlib
open MeasureTheory ProbabilityTheory Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.locallySummableTimeRepresentationActualJumpsV1
    (f g : ℝ≥0 → ℝ) (d : ℝ)
    (hs : ∀ T : ℝ≥0, Summable (fun s : Set.Ioc (0 : ℝ≥0) T => |g s|))
    (heq : ∀ T : ℝ≥0, f T = d * (T : ℝ) +
      ∑' s : Set.Ioc (0 : ℝ≥0) T, g s) :
    ∀ t : ℝ≥0, 0 < t → f t - leftLim f t = g t := by
  sorry
