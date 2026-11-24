-- Prove2me | Theorems.Thm_Kyprianou_Ch02_exercise27JumpTailProbabilityV1
-- name    : Kyprianou.Ch02.exercise27JumpTailProbabilityV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:12:41.471962+00:00
-- url     : https://prove2.me/theorems/52cfefb4-e810-4da4-93d6-dad595c0f9df
-- title:
--   Strict jump-tail probability
-- statement:
--   Use the finite-rate Poisson jump-count law for the strict mark region, or transport the path event from a Levy-Ito representation with the same path law.
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

theorem Kyprianou.Ch02.exercise27JumpTailProbabilityV1
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
    (∀ (t : ℝ≥0) (threshold : ℝ), 0 < threshold →
      P {ω | ∃ s : ℝ≥0, 0 < s ∧ s ≤ t ∧
        ∃ l : ℝ,
          Tendsto (fun u => X u ω)
            (nhdsWithin s (Set.Iio s)) (nhds l) ∧
          threshold < |X s ω - l|} =
      ENNReal.ofReal (1 -
        Real.exp (-(t : ℝ) *
          (ν {x : ℝ | threshold < |x|}).toReal))) := by sorry
