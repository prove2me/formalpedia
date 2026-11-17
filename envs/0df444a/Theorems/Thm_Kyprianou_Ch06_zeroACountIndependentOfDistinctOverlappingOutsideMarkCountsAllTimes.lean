-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfDistinctOverlappingOutsideMarkCountsAllTimes
-- name    : Kyprianou.Ch06.zeroACountIndependentOfDistinctOverlappingOutsideMarkCountsAllTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:16:43.268093+00:00
-- url     : https://prove2.me/theorems/665995c1-e061-48a4-8aae-3a48a7ffe8ae
-- title:
--   Zero A-count independent of genuinely overlapping distinct outside marks at arbitrary times
-- statement:
--   The genuinely unsolved original Chapter 6 zero-A-count independence case for distinct, spatially overlapping outside mark sets B,C observed at arbitrary possibly different times and arbitrary count levels. Disjoint B,C is separately proved from the source finite-rectangle law and the chapter six arbitrary finite disjoint outside cylinder theorem. This child retains all nontrivial overlapping source obligations and does not strengthen the marked-Poisson assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfDistinctOverlappingOutsideMarkCountsAllTimes
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (k l : Nat) (hDistinct : B ≠ C)
    (hOverlap : ¬ Disjoint B C) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t C = l} := by sorry
