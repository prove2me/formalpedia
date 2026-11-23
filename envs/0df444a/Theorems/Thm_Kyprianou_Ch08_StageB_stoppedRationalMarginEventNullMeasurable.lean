-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_stoppedRationalMarginEventNullMeasurable
-- name    : Kyprianou.Ch08.StageB.stoppedRationalMarginEventNullMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:32:21.403409+00:00
-- url     : https://prove2.me/theorems/0cfd64c9-c29c-46c8-8139-c96db1fc5c45
-- title:
--   Lemma 8.2: exact countable rational stopped uniform-gap certificate is null-measurable
-- statement:
--   For a possibly infinite a.e. measurable stopping time and a path with measurable rational coordinates, the event that, on every nonnegative rational time cutoff strictly before the stop, every nonnegative rational observation up to that cutoff lies below a fixed height by some positive reciprocal-integer margin is null measurable. All four quantifiers range over countable types. Use null-measurable preimages under original a.e. coordinate measurability and countable set unions/intersections, preserving strictness.
-- source:
--   Pinned Mathlib NullMeasurableSet.iInter/iUnion and AEMeasurable.nullMeasurableSet_preimage, 0df444a360eaa60ab8c11dca51a86af692955474. Analytic child of generic stoppedStrictPathEventNullMeasurable in Chapter 8 Lemma 8.2.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.stoppedRationalMarginEventNullMeasurable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (h : ℝ)
    (hT : AEMeasurable T P)
    (hf : ∀ r : ℚ, 0 ≤ r →
      AEMeasurable (f (r : ℝ).toNNReal) P) :
    NullMeasurableSet
      {ω : Ω |
        ∀ q : ℚ, 0 ≤ q →
          ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω →
          ∃ n : ℕ,
            ∀ r : ℚ, 0 ≤ r → r ≤ q →
              f (r : ℝ).toNNReal ω <
                h - 1 / (((n + 1 : ℕ) : ℝ))} P := by
  sorry
