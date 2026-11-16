-- Prove2me | Theorems.Thm_Kyprianou_exercise2_4_AllPartsCh02V3
-- name    : Kyprianou.exercise2_4_AllPartsCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:23:46.908704+00:00
-- url     : https://prove2.me/theorems/14556a83-e4b8-429a-a267-9d409e99daea
-- title:
--   Exercise 2.4: uniform closure of cadlag paths and countability of jumps
-- statement:
--   Part (i) establishes closure of right-continuous-with-left-limits paths on the unit interval under uniform convergence; part (ii) proves that jumps larger than any fixed threshold are finite and all discontinuities are countable.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.4, pp. 62-66; author solutions pp. 307-311; corrections recorded where needed

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem exercise2_4_AllPartsCh02V3 :
    let isCadlagOnUnit : (ℝ → ℝ) → Prop := fun f =>
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        ContinuousWithinAt f (Set.Icc t 1) t) ∧
      (∀ t ∈ Set.Ioc (0 : ℝ) 1,
        ∃ l : ℝ,
          Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l))
    ((∀ (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ),
        (∀ n, isCadlagOnUnit (fn n)) →
        (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            |fn n t - f t| < ε) →
        isCadlagOnUnit f) ∧
     (∀ (f : ℝ → ℝ), isCadlagOnUnit f →
        (∀ c : ℝ, 0 < c →
          Set.Finite {t : ℝ |
            t ∈ Set.Ioc (0 : ℝ) 1 ∧
            ∃ l : ℝ,
              Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l) ∧
              c < |f t - l|}) ∧
        Set.Countable {t : ℝ |
          t ∈ Set.Ioc (0 : ℝ) 1 ∧
          ¬ ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) t}))
      := by sorry

end Kyprianou
