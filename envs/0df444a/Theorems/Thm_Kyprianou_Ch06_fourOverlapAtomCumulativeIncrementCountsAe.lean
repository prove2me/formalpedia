-- Prove2me | Theorems.Thm_Kyprianou_Ch06_fourOverlapAtomCumulativeIncrementCountsAe
-- name    : Kyprianou.Ch06.fourOverlapAtomCumulativeIncrementCountsAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:37:13.894204+00:00
-- url     : https://prove2.me/theorems/9b7cc3e9-dfe9-4587-a338-a64659f5a156
-- title:
--   Four overlapping-mark cumulative count cylinder equals the source increment cylinder almost surely
-- statement:
--   From the original Chapter 6 marked-Poisson almost-sure initial count N_0(D)=0 for all marks D, simultaneous arbitrary count observations for the three pre-s disjoint spatial atoms and the one subsequent C-increment are almost surely equivalent to the four source rectangle-increment count constraints.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.fourOverlapAtomCumulativeIncrementCountsAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (s t : NNReal) (x y z w : Nat) :
    ∀ᵐ omega ∂P,
      (N omega s (B \ C) = x ∧
       N omega s (B ∩ C) = y ∧
       N omega s (C \ B) = z ∧
       N omega t C-N omega s C = w) ↔
      (N omega s (B \ C)-N omega 0 (B \ C) = x ∧
       N omega s (B ∩ C)-N omega 0 (B ∩ C) = y ∧
       N omega s (C \ B)-N omega 0 (C \ B) = z ∧
       N omega t C-N omega s C = w) := by sorry
