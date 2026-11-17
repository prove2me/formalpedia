-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfFourOverlapSpacetimeAtomCounts
-- name    : Kyprianou.Ch06.zeroACountIndependentOfFourOverlapSpacetimeAtomCounts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:32:48.350195+00:00
-- url     : https://prove2.me/theorems/fb934a02-c46c-4a1c-a5a6-ce3c47ca9c74
-- title:
--   Zero A-count independent of four compatible space-time atom counts for overlapping outside marks
-- statement:
--   Exactly the original marked-Poisson source Chapter 6 four-compatible-space-time-rectangle factorisation. For arbitrary measurable finite-intensity A, B and C with A disjoint from B and C, zero A-count at arbitrary time r is independent of the complete joint atom counts X=N_s(B\C), Y=N_s(B∩C), Z=N_s(C\B) and W=N_t(C)-N_s(C), with ordered s≤t and arbitrary nonnegative atom count values. The first three rectangles are spatially disjoint and the final C rectangle is temporally disjoint. This retains the genuine positive-intensity overlap case.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfFourOverlapSpacetimeAtomCounts
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
      N omega s (B \ C) = x ∧
      N omega s (B ∩ C) = y ∧
      N omega s (C \ B) = z ∧
      N omega t C - N omega s C = w} =
    P {omega | N omega r A = 0} *
    P {omega |
      N omega s (B \ C) = x ∧
      N omega s (B ∩ C) = y ∧
      N omega s (C \ B) = z ∧
      N omega t C - N omega s C = w} := by sorry
