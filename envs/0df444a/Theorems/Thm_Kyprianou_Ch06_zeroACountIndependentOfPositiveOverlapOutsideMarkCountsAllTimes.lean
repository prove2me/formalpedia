-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfPositiveOverlapOutsideMarkCountsAllTimes
-- name    : Kyprianou.Ch06.zeroACountIndependentOfPositiveOverlapOutsideMarkCountsAllTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:24:07.546809+00:00
-- url     : https://prove2.me/theorems/44c81050-6ce4-4473-a3d1-474d51d4c4f3
-- title:
--   Zero A-count independent of positive-intensity overlapping outside marks at arbitrary times
-- statement:
--   The remaining substantive original Chapter 6 zero A-count independence obligation for distinct, spatially overlapping outside mark sets B and C of strictly positive common intensity, observed at arbitrary potentially different times and with arbitrary nonzero or zero count values. The complementary case of zero overlap intensity is independently source-provable via the original zero-count all-times theorem and disjoint outside count factorisation. This child retains all nontrivial positive-overlap original hypotheses without adding any stochastic independence assumption.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfPositiveOverlapOutsideMarkCountsAllTimes
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (k l : Nat) (hDistinct : B ≠ C)
    (hOverlap : ¬ Disjoint B C) (hPositive : n (B ∩ C) ≠ 0) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t C = l} := by sorry
