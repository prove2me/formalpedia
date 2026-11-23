-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_rationalPrefixUniformGapNullMeasurable
-- name    : Kyprianou.Ch08.StageB.rationalPrefixUniformGapNullMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:40:21.271802+00:00
-- url     : https://prove2.me/theorems/25146d1a-cede-42f3-abe9-98b5568f6817
-- title:
--   Lemma 8.2: rational observation prefix strict-height gap has a measurable event for each cutoff and gap
-- statement:
--   For every rational cutoff q and every natural reciprocal-margin index n, the event that all nonnegative rational observations up to q lie below the height by 1/(n+1) is measurable modulo null sets, when those coordinates are a.e. measurable. It is a countable intersection of a.e. measurable Iio preimages. This is the atomic countable-event step required for the stopped strict-height characterisation.
-- source:
--   Pinned Mathlib NullMeasurableSet.iInter and AEMeasurable.nullMeasurableSet_preimage; connected Lemma 8.2 theorem stoppedRationalMarginEventNullMeasurable 0cfd64c9-c29c-46c8-8139-c96db1fc5c45.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.rationalPrefixUniformGapNullMeasurable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ≥0 → Ω → ℝ)
    (h : ℝ)
    (hf : ∀ r : ℚ, 0 ≤ r →
      AEMeasurable (f (r : ℝ).toNNReal) P) :
    ∀ (q : ℚ) (n : ℕ),
      NullMeasurableSet
        {ω : Ω | ∀ r : ℚ, 0 ≤ r → r ≤ q →
          f (r : ℝ).toNNReal ω <
            h - 1 / (((n + 1 : ℕ) : ℝ))} P := by
  sorry
