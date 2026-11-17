-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfDistinctOutsideMarkCountsAllTimes
-- name    : Kyprianou.Ch06.zeroACountIndependentOfDistinctOutsideMarkCountsAllTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:15:48.101006+00:00
-- url     : https://prove2.me/theorems/9323de17-f526-46e5-8579-edcf03d64692
-- title:
--   Zero A-count independent of observations of distinct outside marks at arbitrary times
-- statement:
--   The irreducible unequal outside-mark-set case of Chapter 6 marked-Poisson independence: zero A-count at arbitrary time r is independent of two possibly overlapping distinct measurable finite-intensity outside mark count observations B and C, at arbitrary times and count levels. The equal mark sets case is separately source-provable by independent consecutive increments and both time orderings. This child preserves the original rectangular point-process law and all genuine distinct-mark obligations.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfDistinctOutsideMarkCountsAllTimes
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (k l : Nat) (hDistinct : B ≠ C) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t C = l} := by sorry
