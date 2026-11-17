-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonZeroIntensityAllCountsVanish
-- name    : Kyprianou.Ch06.markedPoissonZeroIntensityAllCountsVanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:46:47.179098+00:00
-- url     : https://prove2.me/theorems/4d4e6f0a-c4f2-4aa4-8d17-0ce3b5eeb1ef
-- title:
--   Chapter 6 zero-intensity Poisson marks vanish at every time almost surely
-- statement:
--   For the original marked Poisson point process, a measurable mark set of intensity zero has count zero at every time, almost surely. Prove by Poisson zero-count marginals at each natural time, countable almost-sure intersection and monotonicity of the counting process to dominate all real nonnegative times. This is the substantive zero-intensity input to Lemma 6.18.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.markedPoissonZeroIntensityAllCountsVanish
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A : Set E) (hA : MeasurableSet A) (hZero : n A = 0) :
  ∀ᵐ omega ∂P, ∀ t : NNReal, N omega t A = 0 := by sorry
