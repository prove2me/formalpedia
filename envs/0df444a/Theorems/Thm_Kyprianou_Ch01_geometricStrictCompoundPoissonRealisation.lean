-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricStrictCompoundPoissonRealisation
-- name    : Kyprianou.Ch01.geometricStrictCompoundPoissonRealisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:21:56.43906+00:00
-- url     : https://prove2.me/theorems/d7667a08-16d9-408c-ba58-2839bc0dfe33
-- title:
--   Strict geometric law realised as a nonzero-jump compound-Poisson marginal
-- statement:
--   For every geometric success probability strictly between zero and one, the real pushforward of the geometric count distribution equals the time-one marginal of a genuine compound-Poisson driver with positive jump rate, probability jump law and no atom at zero. This is the exact source-faithful representation required for Kyprianou (2006), Exercise 1.2(i).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i): compound-Poisson representation of the geometric distribution.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricStrictCompoundPoissonRealisation
    (p : unitInterval.Elem) (hp : p ≠ 0) (hp1 : (p : ℝ) < 1) :
    ∃ (r : ℝ≥0) (ν' : Measure ℝ) (Ω : Type)
      (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (τ Y : ℕ → Ω → ℝ),
      IsProbabilityMeasure ν' ∧
      IsProbabilityMeasure μ ∧
      0 < r ∧ ν' {0} = 0 ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ ∧
      ((ProbabilityTheory.geometricMeasure p).map
        (fun k : ℕ => (k : ℝ))) =
        μ.map (LevyFoundations.compoundPoisson 0 τ Y (1 : ℝ)) := by
  sorry
