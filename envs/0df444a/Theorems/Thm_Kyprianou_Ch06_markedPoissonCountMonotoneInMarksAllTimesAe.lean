-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonCountMonotoneInMarksAllTimesAe
-- name    : Kyprianou.Ch06.markedPoissonCountMonotoneInMarksAllTimesAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:55:00.576201+00:00
-- url     : https://prove2.me/theorems/59dfcacc-1075-4542-8659-8aa9f054a608
-- title:
--   Chapter 6 marked Poisson pathwise monotonicity across all mark sets and all times
-- statement:
--   From the original marked Poisson finite-additivity path condition, deduce almost surely and simultaneously for every pair of mark sets B⊆C and every deterministic time t, N_t(B)≤N_t(C). The exceptional set is uniform in mark sets and time, allowing application to a sample-dependent marked singleton and first-arrival time.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.markedPoissonCountMonotoneInMarksAllTimesAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N) :
    ∀ᵐ omega ∂P, ∀ (B C : Set E), B ⊆ C →
      ∀ t : NNReal, N omega t B ≤ N omega t C := by sorry
