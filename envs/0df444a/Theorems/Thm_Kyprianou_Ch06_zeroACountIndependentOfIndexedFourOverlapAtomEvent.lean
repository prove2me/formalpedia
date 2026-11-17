-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfIndexedFourOverlapAtomEvent
-- name    : Kyprianou.Ch06.zeroACountIndependentOfIndexedFourOverlapAtomEvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:34:19.029197+00:00
-- url     : https://prove2.me/theorems/50a7afae-47e9-49c1-a8c3-712fd3de5762
-- title:
--   Zero A-count independent of one indexed four-rectangle overlap atom event
-- statement:
--   The original source marked-Poisson four compatible rectangle count independence applies to every indexed atom event in the finite decomposition of two overlapping outside mark counts at ordered times. For a valid atom index the arithmetic constraint is automatic and the source four-rectangle factorisation applies; invalid atom indices describe the empty event. Arbitrary A, B, C, observation times and count values are retained.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfIndexedFourOverlapAtomEvent
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (hst : s ≤ t)
    (k l : Nat) (i : Fin (k+1) × Fin (l+1)) :
    P {omega | N omega r A = 0 ∧
      (i.1 : Nat) + (i.2 : Nat) ≤ l ∧
      N omega s (B \ C) = k-(i.1 : Nat) ∧
      N omega s (B ∩ C) = (i.1 : Nat) ∧
      N omega s (C \ B) = (i.2 : Nat) ∧
      N omega t C - N omega s C = l-(i.1 : Nat)-(i.2 : Nat)} =
    P {omega | N omega r A = 0} *
    P {omega | (i.1 : Nat) + (i.2 : Nat) ≤ l ∧
      N omega s (B \ C) = k-(i.1 : Nat) ∧
      N omega s (B ∩ C) = (i.1 : Nat) ∧
      N omega s (C \ B) = (i.2 : Nat) ∧
      N omega t C - N omega s C = l-(i.1 : Nat)-(i.2 : Nat)} := by sorry
