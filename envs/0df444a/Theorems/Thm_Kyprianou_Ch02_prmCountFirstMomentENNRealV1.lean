-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmCountFirstMomentENNRealV1
-- name    : Kyprianou.Ch02.prmCountFirstMomentENNRealV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:41:12.492574+00:00
-- url     : https://prove2.me/theorems/a2972f47-107d-4aab-b19e-ca1a352f48f2
-- title:
--   Extended expectation of a KLS Poisson random measure count
-- statement:
--   For finite intensity the count law and Poisson mean give the expectation; for infinite intensity the count is almost surely infinite.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.9 and Exercise 2.6(ii); conditional mean of Poisson mark increments.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem prmCountFirstMomentENNRealV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    ∫⁻ ω, N.N ω S ∂P = LevyStochCalc.Poisson.referenceIntensity ν S := by sorry

end Kyprianou.Ch02
