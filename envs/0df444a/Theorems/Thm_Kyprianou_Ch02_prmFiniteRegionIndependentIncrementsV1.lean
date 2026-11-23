-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionIndependentIncrementsV1
-- name    : Kyprianou.Ch02.prmFiniteRegionIndependentIncrementsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T08:56:03.936621+00:00
-- url     : https://prove2.me/theorems/61da0440-abd3-4e34-b648-069afb99c468
-- title:
--   Independent increments for a finite-intensity Poisson stochastic integral
-- statement:
--   Use independent scattering of the Poisson random measure on disjoint time strips, plus measurability of the integral as a functional of the restricted measure.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.8, finite-region Poisson integral; sound decomposition of the Chapter 2 theorem Kyprianou.finiteRegionPoissonIntegralCh02V3 (38df877c-0872-40d5-8b33-bbad3487ba47), itself already linked to Kyprianou.largeJumpProcessLevy (5c06d985-05f1-4c04-aa68-fc6de328bbfa).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionIndependentIncrementsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ProbabilityTheory.HasIndependentIncrements
      (fun (t : ℝ≥0) (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P := by sorry
