-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionStationaryIncrementMarginalLawV2
-- name    : Kyprianou.Ch02.prmFiniteRegionStationaryIncrementMarginalLawV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T11:19:30.564481+00:00
-- url     : https://prove2.me/theorems/7767a6cb-c673-42c5-b6e8-afaf878dced0
-- title:
--   Poisson finite-region StationaryIncrementMarginalLaw
-- statement:
--   Time-shift equality of the full marked Poisson integral increment law. Requires translation-invariance of the intensity and the marked PRM law, plus sample-path strip additivity. With the Proved Chapter 6 stationary-increment conversion, start-at-zero and common measurability, this closes HasStationaryIncrements. This v2 source interface corrects the placement of the parameter X and its exact-equality hypothesis before the theorem conclusion.
-- source:
--   Kyprianou (2006) Chapter 2, finite-activity marked PRM integral; exact Open source-facing increment targets 61da0440 and 84c870a3; reuse proved Ch01 and Ch06 bridges.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionStationaryIncrementMarginalLawV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (X : ℝ≥0 → Ω → ℝ) (hX : X = (fun (q : ℝ≥0) (ω : Ω) =>
      ∫ z in (Set.Ioc (0 : ℝ) (q : ℝ) ×ˢ B), z.2 ∂(N.N ω))) :
    ∀ s t : ℝ≥0,
      P.map (fun (ω : Ω) => X (s + t) ω - X s ω) =
        P.map (X t) := by sorry
