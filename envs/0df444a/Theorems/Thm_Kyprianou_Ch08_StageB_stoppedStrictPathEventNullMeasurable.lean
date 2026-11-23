-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_stoppedStrictPathEventNullMeasurable
-- name    : Kyprianou.Ch08.StageB.stoppedStrictPathEventNullMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:29:10.26321+00:00
-- url     : https://prove2.me/theorems/67941d4c-78d8-4452-8774-492f9a0f098c
-- title:
--   General stopped-path theorem: a.e. right-continuity and compact upper semicontinuity make a strict pre-stop height event null-measurable
-- statement:
--   Given a possibly infinite stopping clock measurable modulo null sets, real path coordinates measurable modulo null sets at nonnegative rational times, and almost-sure right-continuity plus compact-interval upper semicontinuity, the event that the path remains strictly below a real height at all times before the stopping clock is itself measurable modulo null sets. The countable representation tests rational cutoff times strictly below the stop, and on each compact rational cutoff admits a uniform strict gap below the height. This preserves exact strictness even when the supremum reaches the threshold at an isolated point and does not assume an atomless height law.
-- source:
--   Abstract measurable separability/compact extrema theorem using pinned Mathlib upper-semicontinuity and rational-density. Sound independent analytic child for exact source theorem f9a67c26 in Chapter 8 Lemma 8.2.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.stoppedStrictPathEventNullMeasurable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0)
    (h : ℝ)
    (hT : AEMeasurable T P)
    (hf : ∀ r : ℚ, 0 ≤ r →
      AEMeasurable (f (r : ℝ).toNNReal) P)
    (hpath : ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0,
        ContinuousWithinAt (fun s => f s ω) (Set.Ici t) t) ∧
      (∀ z : ℝ≥0,
        UpperSemicontinuousOn (fun s => f s ω) (Set.Icc 0 z))) :
    NullMeasurableSet
      {ω : Ω | ∀ t : ℝ≥0,
        (t : WithTop ℝ≥0) < T ω → f t ω < h} P := by
  sorry
