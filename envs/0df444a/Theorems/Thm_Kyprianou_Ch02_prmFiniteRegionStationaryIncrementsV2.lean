-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionStationaryIncrementsV2
-- name    : Kyprianou.Ch02.prmFiniteRegionStationaryIncrementsV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T11:28:49.034826+00:00
-- url     : https://prove2.me/theorems/130a9be4-af43-46d3-b045-4d9675d3ae09
-- title:
--   Source-exact finite-region marked PRM stationary increments, corrected provider interface
-- statement:
--   Mathematically identical to original prmFiniteRegionStationaryIncrementsV1 (84c870a3), with fully qualified source and minimal KLS Poisson Atomic and StochasticProcess definition providers, following previously ACCEPTED Chapter 2 source-interface repairs. Reduction to a Proved general stationary-increment conversion, fixed-time marked-integral measurability, Proved start-zero and time-shift marginal law.
-- source:
--   Kyprianou (2006) Chapter 2, finite-region Poisson Lévy process, source-equivalent repair of 84c870a3-a119-4157-bcce-28687c1f8ac4.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionStationaryIncrementsV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ProbabilityTheory.HasStationaryIncrements
      (fun (t : ℝ≥0) (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P := by sorry
