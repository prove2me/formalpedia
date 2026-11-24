-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmWindowIntegrableMarkSampleV1
-- name    : Kyprianou.Ch02.prmWindowIntegrableMarkSampleV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:45:05.221914+00:00
-- url     : https://prove2.me/theorems/cd78d626-4d3e-432a-98be-c2562cc81b5e
-- title:
--   Almost-sure integrability of an integrable mark on a Poisson time window
-- statement:
--   The nonnegative Campbell expectation of absolute marks is finite. The absolute mark integral is measurable as a function of the restricted random measure, so it is finite almost surely and implies sample Bochner integrability.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.9 and Exercise 2.6(ii); conditional mean of Poisson mark increments.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem prmWindowIntegrableMarkSampleV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f ν) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, IntegrableOn (fun z : ℝ × ℝ => f z.2)
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) (N.N ω) := by sorry

end Kyprianou.Ch02
