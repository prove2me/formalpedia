-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmSignedMarkIntegralMeasurableFromPosNegV1
-- name    : Kyprianou.Ch02.prmSignedMarkIntegralMeasurableFromPosNegV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T11:37:19.767175+00:00
-- url     : https://prove2.me/theorems/68f60565-3ab0-431a-af8d-597234e23f65
-- title:
--   Signed marked integral measurable from positive and negative lintegrals
-- statement:
--   Given measurability of the positive and negative extended integrals of the restricted real mark coordinate, the signed Bochner set-integral is measurable in the same σ-algebra. Handle the measurable integrability condition and the convention that nonintegrable integral is zero; deduce the result as a piecewise difference of finite toReal parts.
-- source:
--   Kyprianou (2006) Chapter 2 Eq (2.3), marked integrals of arbitrary LevyStochCalc.Poisson.PoissonRandomMeasure.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmSignedMarkIntegralMeasurableFromPosNegV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (hp : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] (fun ω => ∫⁻ z, R.indicator
        (fun z : ℝ × ℝ => ENNReal.ofReal z.2) z ∂(N.N ω)))
    (hn : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] (fun ω => ∫⁻ z, R.indicator
        (fun z : ℝ × ℝ => ENNReal.ofReal (-z.2)) z ∂(N.N ω))) :
    Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
      (fun ω => ∫ z in R, z.2 ∂(N.N ω)) := by sorry
