-- Prove2me | Theorems.Thm_Kyprianou_compoundPoissonDriftCriterionCh02
-- name    : Kyprianou.compoundPoissonDriftCriterionCh02
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:21:46.013213+00:00
-- url     : https://prove2.me/theorems/9af1fadb-972e-4fd5-9d73-a523670f5230
-- title:
--   Lemma 2.13: compound Poisson with drift criterion
-- statement:
--   Lemma 2.13: compound Poisson with drift criterion. Equivalent compound-Poisson-with-drift characteristic law; zero intensity included.
-- source:
--   A. E. Kyprianou (2006), Chapter 2, pp. 33–66

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem compoundPoissonDriftCriterionCh02
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (∃ (d : ℝ) (ν : Measure ℝ),
      ν Set.univ < ⊤ ∧
      ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P.map (X t)) ξ =
          Complex.exp ((((t : ℝ) : ℂ)) *
            (Complex.I * (((d * ξ : ℝ) : ℂ)) +
              ∫ x, (Complex.exp (Complex.I *
                (((ξ * x : ℝ) : ℂ))) - 1) ∂ν))) ↔
      σ = 0 ∧ levyMeasure Set.univ < ⊤ := by sorry

end Kyprianou
