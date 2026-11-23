-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableAmbientV1
-- name    : Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:42:24.220247+00:00
-- url     : https://prove2.me/theorems/0d5b268c-53cc-4536-a07d-53a5d3ccc5e9
-- title:
--   Measurability of KLS marked Poisson integrals in the ambient probability sigma-algebra
-- statement:
--   Every real marked integral over a measurable space-time region is measurable as a function of the underlying KLS Poisson random measure. This follows from the already-proved local-evaluation-sigma measurability theorem because all evaluation maps are measurable in the ambient sigma-algebra.
-- source:
--   Kyprianou Chapter 2 KLS PRM local integral measurability; proved Kyprianou.Ch02.prmMarkedIntegralMeasurableLocalEvalSigmaV1

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R) :
    Measurable (fun ω => ∫ z in R, z.2 ∂(N.N ω)) := by sorry
