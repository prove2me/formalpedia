-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveSmallTimeTestBoundV1
-- name    : Kyprianou.Ch02.positiveSmallTimeTestBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:03:02.653662+00:00
-- url     : https://prove2.me/theorems/c25f0313-926f-4dbd-89b7-67a3722492e8
-- title:
--   Small-time positive marginal first moment bounds interior tests
-- statement:
--   The positive marginal support makes the absolute-radius truncated linear mark dominate the interior positive test almost everywhere. Compare their scaled integrals and pass to the two given limits.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, small-time moment and drift characterisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveSmallTimeTestBoundV1
    (M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ)
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hM : ∀ t, (M t : Measure ℝ) (Set.Iio (0 : ℝ)) = 0)
    (r b : ℝ) (hr : 0 < r) (ts : ℕ → {t : ℝ // 0 < t})
    (hb : Tendsto (fun n => (ts n).val⁻¹ *
      ∫ x in {x : ℝ | |x| < r}, x ∂(M (ts n) : Measure ℝ)) atTop (nhds b))
    (hjump : ∀ f : BoundedContinuousFunction ℝ ℝ,
      (∃ δ > 0, ∀ x, |x| < δ → f x = 0) →
      Tendsto (fun n => (ts n).val⁻¹ * ∫ x, f x ∂(M (ts n) : Measure ℝ))
        atTop (nhds (∫ x, f x ∂ν)))
    (f : BoundedContinuousFunction ℝ ℝ)
    (hf : ∀ x, f x ≤ (Set.Ioo (0 : ℝ) r).indicator id x)
    (hzero : ∃ δ > 0, ∀ x, |x| < δ → f x = 0) :
    (∫ x, f x ∂ν) ≤ b := by
  sorry
