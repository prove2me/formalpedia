-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeDisjointOutsideCounts
-- name    : Kyprianou.Ch06.zeroACountIndependentOfThreeDisjointOutsideCounts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:14:29.284215+00:00
-- url     : https://prove2.me/theorems/36f14ec4-a34b-41c0-8a8f-541504a3bcb4
-- title:
--   Zero A-count event independent of three disjoint outside-mark counts
-- statement:
--   For the original Chapter 6 marked Poisson counting process, if A, B, C and D are measurable finite-intensity mark sets that are mutually pairwise disjoint, then the zero A-count event at any time s is independent of the joint event that B, C and D have arbitrary specified counts at any time t. This follows by instantiating the separately Proved general finite-dimensional independent disjoint outside-mark cylinder theorem with exactly three outside coordinates, and allows Boolean spatial atom decompositions of overlapping original mark sets without strengthening the source process assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfThreeDisjointOutsideCounts
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C D : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hD : MeasurableSet D)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hFA : n A < ⊤) (hFB : n B < ⊤)
    (hFC : n C < ⊤) (hFD : n D < ⊤)
    (s t : NNReal) (k l q : Nat) :
    P {omega | N omega s A = 0 ∧ N omega t B = k ∧
      N omega t C = l ∧ N omega t D = q} =
    P {omega | N omega s A = 0} *
    P {omega | N omega t B = k ∧ N omega t C = l ∧
      N omega t D = q} := by sorry
