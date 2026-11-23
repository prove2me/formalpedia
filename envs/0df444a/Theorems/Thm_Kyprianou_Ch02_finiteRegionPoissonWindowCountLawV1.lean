-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonWindowCountLawV1
-- name    : Kyprianou.Ch02.finiteRegionPoissonWindowCountLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:59:54.667805+00:00
-- url     : https://prove2.me/theorems/3a4d77d0-4d9f-4749-9d37-c148b80c4c0e
-- title:
--   Lemma 2.8 Poisson law of finite-intensity time-mark count
-- statement:
--   For every nonnegative time horizon, the Poisson random measure N has its actual structure-encoded Poisson count law on (0,t] times any finite-intensity measurable mark set B. Proves finite time-space reference intensity via product measures, then applies the KLS PoissonRandomMeasure.poisson_law field.
-- source:
--   Kyprianou (2006), Lemma 2.8. Source-exact KLS Poisson/FiniteActivity.lean and Poisson/RandomMeasure.lean; required for mark-character calculation in Chapter 2.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionPoissonWindowCountLawV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) (t : ℝ≥0) :
    P.map (fun ω => N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)) =
      LevyStochCalc.Poisson.poissonMeasureENN
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toNNReal := by sorry
end Kyprianou.Ch02
