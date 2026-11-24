-- Prove2me | Theorems.Thm_Kyprianou_Ch02_exercise27ContinuousPathsIfV1
-- name    : Kyprianou.Ch02.exercise27ContinuousPathsIfV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:38:29.655611+00:00
-- url     : https://prove2.me/theorems/a8b4e78a-109e-4171-a8e9-e1a571d2cefb
-- title:
--   Zero Levy measure implies continuous paths
-- statement:
--   Zero Levy measure implies continuous paths. Derived from the strict jump-tail probability and countably many reciprocal thresholds.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.7, exact projection of parent 38e63dd3-adcd-4a67-9720-963452efddea

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.exercise27ContinuousPathsIfV1
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, ν, hν⟩ ξ))
    :
    ν = 0 → (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)) := by sorry
