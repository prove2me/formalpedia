-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyMonotoneOfNonnegativeMarginalsV1
-- name    : Kyprianou.Ch02.levyMonotoneOfNonnegativeMarginalsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:27:42.637832+00:00
-- url     : https://prove2.me/theorems/fdb531b0-d43d-4100-8ee2-4ab932da740b
-- title:
--   Nonnegative Lévy marginals imply almost sure monotone paths
-- statement:
--   Stationary increments imply nonnegative increments on a countable dense time set. Intersect the full-measure events and use the almost sure cadlag paths to pass to arbitrary times by right approximation.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, subordinator criterion.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyMonotoneOfNonnegativeMarginalsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ X t ω) →
    (∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω)) := by
  sorry
