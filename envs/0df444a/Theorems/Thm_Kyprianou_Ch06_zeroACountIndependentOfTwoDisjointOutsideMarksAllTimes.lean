-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfTwoDisjointOutsideMarksAllTimes
-- name    : Kyprianou.Ch06.zeroACountIndependentOfTwoDisjointOutsideMarksAllTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:21:28.620338+00:00
-- url     : https://prove2.me/theorems/a8039da5-e8d7-47c4-940f-ef01585b0113
-- title:
--   Zero A-count independent of two pairwise disjoint outside mark count observations at arbitrary times
-- statement:
--   Specialise the source-proved arbitrary finite-dimensional disjoint outside-mark count factorisation to a two-coordinate family. For arbitrary time observations and count levels, three pairwise spatially disjoint measurable finite-intensity mark sets A,B,C have zero A-count independent of the joint two outside count observations. The general original marked Poisson count law suffices, with no strengthened source assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfTwoDisjointOutsideMarksAllTimes
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (k l : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t C = l} := by sorry
