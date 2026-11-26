-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_measurable_compact_supremum_of_evaluation_path
-- name    : ManyServerQED.Scheduling.measurable_compact_supremum_of_evaluation_path
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:00:43.629178+00:00
-- url     : https://prove2.me/theorems/8e8e4604-5263-4ec3-b5d7-81c1449aefd2
-- title:
--   Measurable compact suprema of right-continuous paths
-- statement:
--   A continuous real observable's positive supremum on a compact interval of a right-continuous path can be computed as a measurable functional on the evaluation path space.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem ManyServerQED.Scheduling.measurable_compact_supremum_of_evaluation_path {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (v : E → ℝ) (hv : Continuous v) (T : ℝ≥0) :
    ∃ S : (ℝ≥0 → E) → ℝ≥0∞, Measurable S ∧ ∀ f : ℝ → E,
      (∀ t, 0 ≤ t → ContinuousWithinAt f (Ici t) t) →
      S (fun t : ℝ≥0 => f t) = ⨆ t : ℝ, ⨆ (_ : t ∈ Icc (0:ℝ) T), ENNReal.ofReal (v (f t)) := by sorry
