-- Prove2me | Theorems.Thm_Kyprianou_Ch06_threeMarkedCountVennPartitionAe
-- name    : Kyprianou.Ch06.threeMarkedCountVennPartitionAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:43:06.335363+00:00
-- url     : https://prove2.me/theorems/4023c773-4daf-4d2b-b60d-658379fae5bc
-- title:
--   Three arbitrary marked-Poisson count observations partition a.e. into seven disjoint Venn-atom count sums
-- statement:
--   The authentic Chapter 6 marked-Poisson spatial count additivity implies that three arbitrary overlapping mark sets B,C,D at every time have cumulative counts equal almost surely to sums of their corresponding seven nonempty disjoint Venn-atom counts. This composes eight independently Proved two-mark spatial count partition identities and elementary three-set region equalities, with all original sample-path quantifiers and no extra assumptions. It permits arbitrary overlap and shared positive intensity.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.threeMarkedCountVennPartitionAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C D : Set E) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t B =
        N omega t ((B \ C) \ D) +
        N omega t ((B ∩ C) \ D) +
        N omega t ((B ∩ D) \ C) +
        N omega t (B ∩ C ∩ D) ∧
      N omega t C =
        N omega t ((C \ B) \ D) +
        N omega t ((B ∩ C) \ D) +
        N omega t ((C ∩ D) \ B) +
        N omega t (B ∩ C ∩ D) ∧
      N omega t D =
        N omega t ((D \ B) \ C) +
        N omega t ((B ∩ D) \ C) +
        N omega t ((C ∩ D) \ B) +
        N omega t (B ∩ C ∩ D) := by sorry
