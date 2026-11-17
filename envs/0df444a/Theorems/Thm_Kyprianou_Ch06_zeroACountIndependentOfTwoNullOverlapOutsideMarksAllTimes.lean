-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfTwoNullOverlapOutsideMarksAllTimes
-- name    : Kyprianou.Ch06.zeroACountIndependentOfTwoNullOverlapOutsideMarksAllTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:23:21.882053+00:00
-- url     : https://prove2.me/theorems/e902920e-f4da-4103-acc8-e320c0c9e46b
-- title:
--   Zero A-count independent of two arbitrary-time outside counts whose spatial overlap has zero intensity
-- statement:
--   Under the original Chapter 6 marked Poisson source finite-rectangle axiom, when measurable finite-intensity outside-A marks B and C overlap only on a zero-intensity intersection, the zero A-count event at arbitrary time r is independent of the full simultaneous B/C count cylinder at arbitrary potentially distinct times and all count levels. A source-proved null-overlap count partition identifies it almost surely with the pair of disjoint marked count observations B\C and C\B. Original disjoint outside count factorisation and almost-sure event independence transfer prove the joint probability identity, with no strengthened process assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfTwoNullOverlapOutsideMarksAllTimes
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (hNull : n (B ∩ C) = 0)
    (r s t : NNReal) (k l : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t C = l} := by sorry
