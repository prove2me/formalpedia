-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeConsecutiveOutsideMarkIncrements
-- name    : Kyprianou.Ch06.zeroACountIndependentOfThreeConsecutiveOutsideMarkIncrements
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:21:30.638326+00:00
-- url     : https://prove2.me/theorems/5c2d1d4e-da8d-45da-bcd0-e53d4f952e58
-- title:
--   Zero A-count independent of three consecutive time-separated outside B-increment counts
-- statement:
--   The exact Chapter 6 marked-Poisson finite compatible rectangle law implies independence of the cumulative zero A-count at time r from three consecutive B-increment counts over [0,s], (s,t] and (t,u]. No distinct-mark requirement between those three increments is needed because their time intervals are pairwise disjoint; B is disjoint from A. Handles arbitrary nonnegative count levels and all ordered times s≤t≤u, from an independently Proved general finite-rectangle source theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfThreeConsecutiveOutsideMarkIncrements
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B)
    (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t u : NNReal) (hst : s ≤ t) (htu : t ≤ u)
    (k l q : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B-N omega 0 B = k ∧
      N omega t B-N omega s B = l ∧
      N omega u B-N omega t B = q} =
    P {omega | N omega r A = 0} *
      P {omega |
        N omega s B-N omega 0 B = k ∧
        N omega t B-N omega s B = l ∧
        N omega u B-N omega t B = q} := by sorry
