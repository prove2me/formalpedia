-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionStationaryWindowLawKLSV1
-- name    : Kyprianou.Ch02.prmFiniteRegionStationaryWindowLawKLSV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:49:21.767378+00:00
-- url     : https://prove2.me/theorems/f0365e45-30c4-44d3-a07e-2980ad0497b8
-- title:
--   Stationary law of finite-intensity marked Poisson integrals on shifted time windows, KLS provider
-- statement:
--   For the source-correct LevyStochCalc.Poisson.PoissonRandomMeasure in Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure, the signed real marked Poisson integral over (s,s+t]×B has the same law as over (0,t]×B. This requires approximation by finite simple marked-window count sums and passage to the limit in probability under finite intensity ν B<∞. Already proved Kyprianou.Ch02.prmFiniteSimpleMarkedSumStationaryAndMeasurableV1 and Kyprianou.Ch02.prmFiniteWindowDiracLawV1 supply building blocks. This corrects the older source imported via Definition Def_LevyStochCalc_Poisson_Atomic_F000, which remote compilation did not resolve.
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3), finite-activity compound Poisson stationary window laws; mission ed6e9edb-945b-4dc1-bb4b-3eed54f89dd0.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionStationaryWindowLawKLSV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ s t : ℝ≥0,
      P.map (fun (ω : Ω) =>
        ∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)) =
      P.map (fun (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)) := by sorry
