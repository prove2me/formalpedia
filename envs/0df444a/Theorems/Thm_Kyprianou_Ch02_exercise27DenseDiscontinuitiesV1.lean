-- Prove2me | Theorems.Thm_Kyprianou_Ch02_exercise27DenseDiscontinuitiesV1
-- name    : Kyprianou.Ch02.exercise27DenseDiscontinuitiesV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:12:37.840799+00:00
-- url     : https://prove2.me/theorems/d9f7f3dc-2f14-4890-865f-9dd8623039d6
-- title:
--   Dense discontinuities under infinite jump activity
-- statement:
--   Apply strict-tail jump probabilities to rational subintervals using stationary increments and let the threshold decrease to zero; intersect the resulting countable full-measure events.
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

theorem Kyprianou.Ch02.exercise27DenseDiscontinuitiesV1
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
    (ν Set.univ = ⊤ →
      ∀ᵐ ω ∂P,
        closure {t : ℝ≥0 |
          ¬ ContinuousAt (fun s : ℝ≥0 => X s ω) t} =
          Set.univ)
 := by sorry
