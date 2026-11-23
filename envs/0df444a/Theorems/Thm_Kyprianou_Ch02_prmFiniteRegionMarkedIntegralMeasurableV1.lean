-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionMarkedIntegralMeasurableV1
-- name    : Kyprianou.Ch02.prmFiniteRegionMarkedIntegralMeasurableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T11:16:29.389003+00:00
-- url     : https://prove2.me/theorems/b6735137-f69c-4aa9-9964-87f46af8dd30
-- title:
--   Poisson finite-region MarkedIntegralMeasurable
-- statement:
--   Measurability of the finite-window marked Poisson integral at every fixed nonnegative time. Derive using measurable PRM evaluation and bounded-region atomic approximation. A shared prerequisite for both independent and stationary increments.
-- source:
--   Kyprianou (2006) Chapter 2, finite-activity marked PRM integral; exact Open source-facing increment targets 61da0440 and 84c870a3; reuse proved Ch01 and Ch06 bridges.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionMarkedIntegralMeasurableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ q : ℝ≥0, Measurable
      (fun (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (q : ℝ) ×ˢ B), z.2 ∂(N.N ω)) := by sorry
