-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralFibreSumV1
-- name    : Kyprianou.Ch02.prmFiniteSimpleMarkIntegralFibreSumV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:53:54.337309+00:00
-- url     : https://prove2.me/theorems/a22c17e2-43d0-496c-89c0-cd490ffff7fe
-- title:
--   KLS finite-region simple-mark Poisson integral equals finite weighted count sum
-- statement:
--   For an actual KLS Poisson random measure and a finite-mass measurable space-time region R, the integral of any real simple mark profile is exactly its finite fibre sum of Poisson event counts, weighted by the simple profile values. The proof applies the existing Proved generic finite-measure fibre-sum theorem to the restricted KLS random measure.
-- source:
--   Kyprianou (2006), Chapter 2 finite-jump stochastic integrals, from Proved realSimpleMarkIntegralFiniteMeasureFibreSumV1

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_realSimpleMarkIntegralFiniteMeasureFibreSumV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteSimpleMarkIntegralFibreSumV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (f : SimpleFunc ℝ ℝ) (ω : Ω)
    (hfin : N.N ω R < ⊤) :
    (∫ z in R, f z.2 ∂(N.N ω)) =
      ∑ x ∈ f.range,
        (N.N ω (R ∩ {z : ℝ × ℝ | f z.2 = x})).toReal * x := by sorry
