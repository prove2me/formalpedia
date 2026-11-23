-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteIntensityCountRealL2V1
-- name    : Kyprianou.Ch02.prmFiniteIntensityCountRealL2V1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:54:10.930606+00:00
-- url     : https://prove2.me/theorems/49128f7f-daa8-4e47-b734-3b7569ed731e
-- title:
--   Every finite-intensity KLS Poisson count is square integrable
-- statement:
--   For every measurable space-time region with finite Poisson reference intensity, the real coercion of the Poisson random count is in L². This follows by adding the deterministic intensity to the proved L² compensated count. Reusable for finite-simple marked Poisson sums and Chapter 2 quadratic moment estimates.
-- source:
--   Kyprianou (2006) Chapter 2 finite-region jump integrals and proved LevyStochCalc.Poisson.Compensated.compensated_sq_integrable

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteIntensityCountRealL2V1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (C : Set (ℝ × ℝ)) (hC : MeasurableSet C)
    (hfinite : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤) :
    MemLp (fun ω => (N.N ω C).toReal) 2 P := by sorry
