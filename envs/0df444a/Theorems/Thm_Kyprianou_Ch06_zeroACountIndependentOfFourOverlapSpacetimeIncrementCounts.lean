-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfFourOverlapSpacetimeIncrementCounts
-- name    : Kyprianou.Ch06.zeroACountIndependentOfFourOverlapSpacetimeIncrementCounts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:39:08.649198+00:00
-- url     : https://prove2.me/theorems/2451ab63-e77c-4ccb-997d-8cc22fe8b8d2
-- title:
--   Zero A-count independent of four compatible outside increment rectangles for overlapping mark sets
-- statement:
--   Original Chapter 6 marked-Poisson count independence for four compatible time-space rectangle increments: zero A-count on [0,r] is independent of the source increments on B\C, B∩C, C\B over [0,s] and C over (s,t], even if B and C share strictly positive intensity. Three separately proved structural lemmas verify the exact time/mark validity, A-external disjointness and rectangle compatibility premises of the original point-process law. No strengthened stochastic assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfFourOverlapSpacetimeIncrementCounts
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (hst : s ≤ t)
    (x y z w : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s (B \ C)-N omega 0 (B \ C) = x ∧
      N omega s (B ∩ C)-N omega 0 (B ∩ C) = y ∧
      N omega s (C \ B)-N omega 0 (C \ B) = z ∧
      N omega t C-N omega s C = w} =
    P {omega | N omega r A = 0} *
    P {omega |
      N omega s (B \ C)-N omega 0 (B \ C) = x ∧
      N omega s (B ∩ C)-N omega 0 (B ∩ C) = y ∧
      N omega s (C \ B)-N omega 0 (C \ B) = z ∧
      N omega t C-N omega s C = w} := by sorry
