-- Prove2me | Theorems.Thm_Kyprianou_Ch06_overlappingMarkedCountSpatialPartitionAe
-- name    : Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:02:16.118755+00:00
-- url     : https://prove2.me/theorems/26c9fa5e-9f39-4933-b913-2b6cb7ce647d
-- title:
--   Two overlapping marked-Poisson spatial count sets decompose into three disjoint atoms almost surely
-- statement:
--   For a Chapter 6 marked Poisson point process and arbitrary mark sets B,C, each count process N_t(B) is almost surely the sum of counts on disjoint cells B\C and B∩C, and N_t(C) similarly decomposes into C\B and B∩C, simultaneously at all times. This is the exact source PPP pathwise finite additivity applied to a Boolean spatial partition; a bridge towards two-coordinate overlapping mark count independence and full outside-mark finite-dimensional factorisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t B = N omega t (B \ C) + N omega t (B ∩ C) ∧
      N omega t C = N omega t (C \ B) + N omega t (B ∩ C) := by sorry
