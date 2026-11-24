-- Prove2me | Theorems.Thm_Kyprianou_Ch02_negativeSupportFixedCutoffFromMarginalTestsV1
-- name    : Kyprianou.Ch02.negativeSupportFixedCutoffFromMarginalTestsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:55:31.495576+00:00
-- url     : https://prove2.me/theorems/0acc7216-6313-4844-9ca0-cffea394b5c9
-- title:
--   Nonnegative small-time marginals force each fixed negative Lévy tail to be null
-- statement:
--   Use a bounded continuous nonnegative cutoff separating x<-r. Each marginal integral is zero by its nonnegative support. The limiting integral against the Lévy measure is zero, and the cutoff is integrable because it vanishes near zero. Its strict positivity below -r forces that fixed negative tail to be null. Countable thresholds in the parent recover all negative support.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; small-time marginal test necessity, parent cee5c65f-db82-4515-8f93-f2ed6c878db1.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem Kyprianou.Ch02.negativeSupportFixedCutoffFromMarginalTestsV1
    (M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ)
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hS : ∀ t, (M t : Measure ℝ) (Set.Iio (0 : ℝ)) = 0)
    (ts : ℕ → {t : ℝ // 0 < t})
    (hjump : ∀ f : BoundedContinuousFunction ℝ ℝ,
      (∃ r > 0, ∀ x, |x| < r → f x = 0) →
      Tendsto (fun n => (ts n).val⁻¹ *
        ∫ x, f x ∂(M (ts n) : Measure ℝ))
        atTop (nhds (∫ x, f x ∂ν)))
    (r : ℝ) (hr : 0 < r) :
    ∀ᵐ x ∂ν, -r ≤ x := by sorry
