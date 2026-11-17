-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfTwoOutsideCountsAllTimes
-- name    : Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideCountsAllTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:08:10.762736+00:00
-- url     : https://prove2.me/theorems/aaf1505b-fb7b-4104-93a2-b80660079684
-- title:
--   Zero A-count independent of two possibly overlapping outside-A count observations at arbitrary times
-- statement:
--   Prove that an original Chapter 6 marked Poisson point process has zero A-count at any deterministic time r independent of any two outside-A count observations of measurable finite-intensity sets B and C, at arbitrary possibly distinct observation times s and t, with arbitrary integer counts. The two outside sets may overlap spatially. The original source law prescribes independent counts on disjoint space-time rectangles; proving this helper requires finite atomisation of overlapping B/C mark sets and the two observation intervals, then finite partition summation. No new process independence premise or strengthened finite-intensity or first-mark hypothesis is used. This isolates the genuine remaining rectangular Poisson calculation for the original Lemma 6.18 first-arrival independence.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideCountsAllTimes
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (k l : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t C = l} := by sorry
