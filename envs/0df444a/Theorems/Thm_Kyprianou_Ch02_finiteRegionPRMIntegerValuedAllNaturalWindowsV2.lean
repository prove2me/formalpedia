-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPRMIntegerValuedAllNaturalWindowsV2
-- name    : Kyprianou.Ch02.finiteRegionPRMIntegerValuedAllNaturalWindowsV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:24:53.313804+00:00
-- url     : https://prove2.me/theorems/3942d588-8e51-4acc-a367-80d2f3cc5cf0
-- title:
--   Integer-valued PRM restrictions on all natural windows, source interface v2
-- statement:
--   On one common full probability event, each natural bounded time-mark window has an integer-valued Poisson random measure restriction. Applies the source KLS integer-valued window argument and countable intersection. Same exact type as V1 with a single KLS source Definition provider and a qualified declaration, to avoid a remote validation failure resolving the first authored target.
-- source:
--   Kyprianou Chapter 2 Lemma 2.8; KLS Poisson/Atomic.lean. V2 source-interface repair for V1 (bae0bc28).

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.finiteRegionPRMIntegerValuedAllNaturalWindowsV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℕ,
      LevyStochCalc.Probability.IsIntegerValued
        ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) := by sorry
