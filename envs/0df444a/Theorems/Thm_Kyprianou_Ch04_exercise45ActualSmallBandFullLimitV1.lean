-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45ActualSmallBandFullLimitV1
-- name    : Kyprianou.Ch04.exercise45ActualSmallBandFullLimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:29:47.628049+00:00
-- url     : https://prove2.me/theorems/23dded9e-ed1e-5e7d-8dcf-e96af581ea79
-- title:
--   Full real-cutoff small-jump limit on the original Poisson space
-- statement:
--   The centred small-jump band has an almost sure simultaneous full-cutoff limit with right-continuous paths. Use independent disjoint mark regions, maximal inequalities and a countable cutoff grid.
-- source:
--   Kyprianou (2006), Exercise 4.5 and Levy-Ito decomposition, Chapter 2.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45ActualSmallBandFullLimitV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hZero : ∀ᵐ w ∂P, N.N w ({0} ×ˢ (Set.univ : Set ℝ)) = 0) :
    ∃ Z : NNReal → Ω → ℝ, ∀ᵐ w ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun s => Z s w) (Ici t) t ∧
      Tendsto (fun e : ℝ =>
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
          z.2 ∂(N.N w)) -
        (t : ℝ) * ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (Z t w)) := by
  sorry
end Kyprianou.Ch04
