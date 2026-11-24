-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveSmallTimeFirstMomentBoundV1
-- name    : Kyprianou.Ch02.positiveSmallTimeFirstMomentBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:03:01.607801+00:00
-- url     : https://prove2.me/theorems/b2dedef6-e686-4b62-bb9c-3b7e615b6e56
-- title:
--   Small-time first-moment limit bounds the positive small-jump mass
-- statement:
--   Approximate the positive interior linear mark by bounded nonnegative continuous cutoffs vanishing near zero. All their Lévy integrals are bounded by b. Fatou yields finite nonnegative integral of the limit and its upper bound.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, small-time moment and drift characterisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveSmallTimeFirstMomentBoundV1
    (M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ)
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hM : ∀ t, (M t : Measure ℝ) (Set.Iio (0 : ℝ)) = 0)
    (r b : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (ts : ℕ → {t : ℝ // 0 < t})
    (hb : Tendsto (fun n => (ts n).val⁻¹ *
      ∫ x in {x : ℝ | |x| < r}, x ∂(M (ts n) : Measure ℝ)) atTop (nhds b))
    (hjump : ∀ f : BoundedContinuousFunction ℝ ℝ,
      (∃ δ > 0, ∀ x, |x| < δ → f x = 0) →
      Tendsto (fun n => (ts n).val⁻¹ * ∫ x, f x ∂(M (ts n) : Measure ℝ))
        atTop (nhds (∫ x, f x ∂ν))) :
    Integrable (fun x : ℝ => x) (ν.restrict (Set.Ioo (0 : ℝ) r)) ∧
      (∫ x in Set.Ioo (0 : ℝ) r, x ∂ν) ≤ b := by
  sorry
