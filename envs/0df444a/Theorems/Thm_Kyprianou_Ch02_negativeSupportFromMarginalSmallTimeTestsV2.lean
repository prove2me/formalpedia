-- Prove2me | Theorems.Thm_Kyprianou_Ch02_negativeSupportFromMarginalSmallTimeTestsV2
-- name    : Kyprianou.Ch02.negativeSupportFromMarginalSmallTimeTestsV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:47:32.880931+00:00
-- url     : https://prove2.me/theorems/cee5c65f-db82-4515-8f93-f2ed6c878db1
-- title:
--   Positive marginal probability measures imply nonnegative Lévy support
-- statement:
--   Use nonnegative bounded continuous tests supported strictly below zero and vanishing near zero. Their integrals against every marginal vanish, so the corresponding integrals against the Lévy measure vanish. Exhaust the negative half-line with countably many strict negative tails; the tests are integrable because the Lévy measure is finite away from zero.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, via the Lévy–Khintchine small-time extraction and uniqueness.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem Kyprianou.Ch02.negativeSupportFromMarginalSmallTimeTestsV2
    (M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ)
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hS : ∀ t, (M t : Measure ℝ) (Set.Iio (0 : ℝ)) = 0)
    (ts : ℕ → {t : ℝ // 0 < t})
    (hjump : ∀ f : BoundedContinuousFunction ℝ ℝ,
      (∃ r > 0, ∀ x, |x| < r → f x = 0) →
      Tendsto (fun n => (ts n).val⁻¹ *
        ∫ x, f x ∂(M (ts n) : Measure ℝ))
        atTop (nhds (∫ x, f x ∂ν))) :
    ν (Set.Iio (0 : ℝ)) = 0 := by
  sorry
