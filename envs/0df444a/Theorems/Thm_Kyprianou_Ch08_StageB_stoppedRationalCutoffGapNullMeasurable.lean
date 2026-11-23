-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_stoppedRationalCutoffGapNullMeasurable
-- name    : Kyprianou.Ch08.StageB.stoppedRationalCutoffGapNullMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:40:28.646251+00:00
-- url     : https://prove2.me/theorems/c84abbdf-a2bd-43cc-9b3d-f75432fc14aa
-- title:
--   Lemma 8.2: strict pre-stopping rational cutoff and existential uniform gap event is measurable modulo null sets
-- statement:
--   For a fixed rational cutoff q, the implication that whenever q is nonnegative and earlier than the possibly infinite stopping time there exists a uniform reciprocal-integer margin for all rational observations up to q is measurable modulo null sets. Combine the original clock's a.e. measurable upper-threshold event with a countable union of rational-prefix events, and handle nonpositive cutoffs as trivial.
-- source:
--   Pinned Mathlib NullMeasurableSet.iUnion, complementation and union; child rationalPrefixUniformGapNullMeasurable in the linked Chapter 8 Lemma 8.2 branch.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.stoppedRationalCutoffGapNullMeasurable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (h : ℝ)
    (hT : AEMeasurable T P)
    (hf : ∀ r : ℚ, 0 ≤ r →
      AEMeasurable (f (r : ℝ).toNNReal) P) :
    ∀ q : ℚ,
      NullMeasurableSet
        {ω : Ω | 0 ≤ q →
          ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω →
          ∃ n : ℕ, ∀ r : ℚ, 0 ≤ r → r ≤ q →
            f (r : ℝ).toNNReal ω <
              h - 1 / (((n + 1 : ℕ) : ℝ))} P := by
  sorry
