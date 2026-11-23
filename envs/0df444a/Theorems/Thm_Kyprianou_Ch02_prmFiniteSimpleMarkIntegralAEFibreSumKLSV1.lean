-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralAEFibreSumKLSV1
-- name    : Kyprianou.Ch02.prmFiniteSimpleMarkIntegralAEFibreSumKLSV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:17:08.303215+00:00
-- url     : https://prove2.me/theorems/00be6015-5c7e-4477-a807-1cebbb5a310b
-- title:
--   Almost-sure finite-simple signed Poisson marked integral equals weighted fibre-count sum
-- statement:
--   On the event where a finite-intensity region R has finite Poisson count, a signed real simple-mark set integral equals sum over its finite mark fibres of measured counts times marks. The required pointwise identity is already Proved in Kyprianou.Ch02.prmFiniteSimpleMarkIntegralFibreSumV1 and finite-count conull event is Proved in Kyprianou.Ch02.prmFiniteRegionAllMeasurableCountNatV1. Exact KLS provider. Parent of Eq (2.3) stationary mark law.
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteSimpleMarkIntegralAEFibreSumKLSV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤)
    (f : SimpleFunc ℝ ℝ) :
    ∀ᵐ ω ∂P, (∫ z in R, f z.2 ∂(N.N ω)) =
      ∑ x ∈ f.range,
        (N.N ω (R ∩ {z : ℝ × ℝ | f z.2 = x})).toReal * x := by sorry
