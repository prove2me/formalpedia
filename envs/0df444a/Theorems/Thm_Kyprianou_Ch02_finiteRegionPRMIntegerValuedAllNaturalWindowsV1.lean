-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPRMIntegerValuedAllNaturalWindowsV1
-- name    : Kyprianou.Ch02.finiteRegionPRMIntegerValuedAllNaturalWindowsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T10:07:21.336689+00:00
-- url     : https://prove2.me/theorems/bae0bc28-ec81-437e-8e2d-ba41326e3c4c
-- title:
--   Poisson random measure integer-valued on all natural windows
-- statement:
--   On one common full probability event, each natural bounded time-mark window has an integer-valued Poisson random measure restriction. Applies the source KLS integer-valued window argument and countable intersection.
-- source:
--   Kyprianou Chapter 2 Lemma 2.8; KLS Poisson/Atomic.lean.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionPRMIntegerValuedAllNaturalWindowsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℕ,
      LevyStochCalc.Probability.IsIntegerValued
        ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) := by sorry
end Kyprianou.Ch02
