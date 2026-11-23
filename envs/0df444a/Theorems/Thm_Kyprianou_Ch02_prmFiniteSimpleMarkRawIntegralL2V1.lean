-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkRawIntegralL2V1
-- name    : Kyprianou.Ch02.prmFiniteSimpleMarkRawIntegralL2V1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:04:56.334225+00:00
-- url     : https://prove2.me/theorems/ca5c2ea4-16e6-4c01-8c44-a2154e911a04
-- title:
--   KLS finite-intensity Poisson simple-mark integrals have a finite second moment
-- statement:
--   For an actual KLS Poisson random measure on a finite-intensity measurable space-time set, integrating any finite-range measurable real mark is square-integrable under the probability law. Its proof combines the already proved exact finite fibre-sum representation with the already proved L2 bound for finite weighted Poisson counts.
-- source:
--   Kyprianou (2006), Chapter 2, Poisson finite-activity marked integrals and L2 estimates

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralFibreSumV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteWeightedCountSumL2V1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteSimpleMarkRawIntegralL2V1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (hfinite : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤)
    (f : SimpleFunc ℝ ℝ) :
    MemLp (fun ω => ∫ z in R, f z.2 ∂(N.N ω)) 2 P := by sorry
