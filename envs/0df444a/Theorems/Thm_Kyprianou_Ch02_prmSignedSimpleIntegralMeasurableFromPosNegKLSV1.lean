-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmSignedSimpleIntegralMeasurableFromPosNegKLSV1
-- name    : Kyprianou.Ch02.prmSignedSimpleIntegralMeasurableFromPosNegKLSV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:26:30.442104+00:00
-- url     : https://prove2.me/theorems/20967e72-6693-4652-84f0-db655ff65a41
-- title:
--   Signed simple Poisson integral locally measurable from positive and negative lintegrals
-- statement:
--   Generalize already Proved Kyprianou.Ch02.prmSignedMarkIntegralMeasurableFromPosNegV1 to a real simple mark f z.2. Given measurable positive/negative lintegrals and the helper integrableSimpleMarkIffLintegralPartsFiniteV1, use integral_eq_lintegral_pos_part_sub_lintegral_neg_part, integral_undef and measurable ite on the integrability event. This is the sole analytic child of Kyprianou.Ch02.prmFiniteSimpleMarkIntegralMeasurableKLSV1 and Eq. (2.3).
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3), KLS PRM measurable random integrals.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmSignedSimpleIntegralMeasurableFromPosNegKLSV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (f : SimpleFunc ℝ ℝ)
    (hp : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
      (fun ω => ∫⁻ z, R.indicator
        (fun z : ℝ × ℝ => ENNReal.ofReal (f z.2)) z ∂(N.N ω)))
    (hn : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
      (fun ω => ∫⁻ z, R.indicator
        (fun z : ℝ × ℝ => ENNReal.ofReal (-(f z.2))) z ∂(N.N ω))) :
    Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
      (fun ω => ∫ z in R, f z.2 ∂(N.N ω)) := by sorry
