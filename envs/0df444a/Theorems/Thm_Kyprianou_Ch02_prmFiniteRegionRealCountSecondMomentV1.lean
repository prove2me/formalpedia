-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionRealCountSecondMomentV1
-- name    : Kyprianou.Ch02.prmFiniteRegionRealCountSecondMomentV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:28:42.091008+00:00
-- url     : https://prove2.me/theorems/516a8bc4-e7ba-46a5-a3b8-e61cebf895d5
-- title:
--   Raw KLS Poisson count has second moment intensity squared plus intensity
-- statement:
--   Every finite-intensity KLS Poisson count has real second moment λ²+λ. This is derived directly from already Proved compensated-count mean zero, variance λ, and KLS count L2 integrability, preserving the original source random measure. It is a reusable quantitative precursor to finite simple-mark Campbell estimates.
-- source:
--   Kyprianou (2006), Chapter 2; Poisson count second moments and Campbell formula

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionRealCountSecondMomentV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (hfinite : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤) :
    (∫ ω, ((N.N ω R).toReal) ^ 2 ∂P) =
      (LevyStochCalc.Poisson.referenceIntensity ν R).toReal ^ 2 +
        (LevyStochCalc.Poisson.referenceIntensity ν R).toReal := by sorry
