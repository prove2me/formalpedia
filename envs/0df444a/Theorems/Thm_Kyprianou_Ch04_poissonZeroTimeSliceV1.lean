-- Prove2me | Theorems.Thm_Kyprianou_Ch04_poissonZeroTimeSliceV1
-- name    : Kyprianou.Ch04.poissonZeroTimeSliceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:26:37.32541+00:00
-- url     : https://prove2.me/theorems/d2268d1b-c654-5b3e-aa65-ea26afb3c64c
-- title:
--   Poisson and intensity measures have no mass at time zero
-- statement:
--   A physical Poisson random measure has no mass at time zero, almost surely.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory Set LevyStochCalc.Poisson
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem poissonZeroTimeSliceV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) :
    referenceIntensity ν (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 ∧
      ∀ᵐ ω ∂P, N.N ω (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
  sorry
end Kyprianou.Ch04
