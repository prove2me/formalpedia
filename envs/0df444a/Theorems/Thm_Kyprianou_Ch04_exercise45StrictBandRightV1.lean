-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45StrictBandRightV1
-- name    : Kyprianou.Ch04.exercise45StrictBandRightV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:38:07.57824+00:00
-- url     : https://prove2.me/theorems/5d594f60-8b27-5992-a612-913a133ab3ce
-- title:
--   Strict-cutoff compensated Poisson band is right continuous almost surely
-- statement:
--   Use finite-region cadlag regularity, and eliminate the time-zero slice with the null-origin assumption.
-- source:
--   Kyprianou (2006), Exercise 4.5 proof auxiliary

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45StrictBandRightV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hZero : ∀ᵐ w ∂P, N.N w ({0} ×ˢ (univ : Set ℝ)) = 0)
    (e : ℝ) (he : 0 < e) :
    ∀ᵐ w ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun s : NNReal =>
        (∫ z in Icc (0:ℝ) (s:ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
          z.2 ∂(N.N w)) - (s:ℝ)*∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν)
        (Ici t) t := by sorry
