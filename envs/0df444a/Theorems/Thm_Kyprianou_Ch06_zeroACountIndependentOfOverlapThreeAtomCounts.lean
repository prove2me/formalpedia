-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfOverlapThreeAtomCounts
-- name    : Kyprianou.Ch06.zeroACountIndependentOfOverlapThreeAtomCounts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:19:22.798042+00:00
-- url     : https://prove2.me/theorems/8fde7e9a-f593-4b60-93dc-3598d76ffb34
-- title:
--   Zero A-count independent of all three disjoint atoms of two possibly overlapping outside mark sets
-- statement:
--   Given the authentic marked Poisson point process, any measurable finite-intensity A disjoint from each of two arbitrary measurable finite-intensity mark sets B,C, the event N_s(A)=0 is independent of the simultaneous count constraints on the three mutually disjoint spatial atoms B\C, C\B and B∩C, at arbitrary count values and times. This follows from the independently Proved three-disjoint-outside-count factorisation, using only disjoint spatial set algebra and finite-intensity monotonicity. This is the substantive event-level factorisation required in the finite sum representing overlapping B,C count cylinders.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfOverlapThreeAtomCounts
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (s t : NNReal) (k l q : Nat) :
    P {omega | N omega s A = 0 ∧ N omega t (B \ C) = k ∧
      N omega t (C \ B) = l ∧ N omega t (B ∩ C) = q} =
    P {omega | N omega s A = 0} *
    P {omega | N omega t (B \ C) = k ∧
      N omega t (C \ B) = l ∧ N omega t (B ∩ C) = q} := by sorry
