-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmKLSFiniteSimpleFibreWeightedCountCharV1
-- name    : Kyprianou.Ch02.prmKLSFiniteSimpleFibreWeightedCountCharV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:10:20.363312+00:00
-- url     : https://prove2.me/theorems/93fcc15e-eb60-43c4-8044-dfb0d987fcc3
-- title:
--   Exact finite weighted Poisson mark-fibre count characteristic exponent
-- statement:
--   For a real simple-mark f and finite ν(B), disjoint mark fibres B∩{f=x} have independent Poisson counts (N.independent_disjoint). Use Proved Kyprianou.Ch02.finiteRegionPoissonCountCharacteristicV1, independent-sum characteristic product and Complex.exp_sum to derive the exact finite sum exponent. Source provider KLS only. This theorem is a direct child of the optional Kyprianou.Ch02.prmFiniteSimpleMarkCharExponentKLSV1 on Chapter 2 mission.
-- source:
--   Kyprianou (2006) Chapter 2, finite-activity Poisson exponent.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmKLSFiniteSimpleFibreWeightedCountCharV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : SimpleFunc ℝ ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (fun (ω : Ω) =>
      ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal)) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∑ x ∈ f.range, ((((ν (B ∩ {y : ℝ | f y = x})).toReal : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1))) := by sorry
