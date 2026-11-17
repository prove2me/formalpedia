-- Prove2me | Theorems.Thm_Kyprianou_Ch06_nullIntensityOverlapCountsEqualDisjointPartsAe
-- name    : Kyprianou.Ch06.nullIntensityOverlapCountsEqualDisjointPartsAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:20:11.618053+00:00
-- url     : https://prove2.me/theorems/136e4c57-f488-4e8f-a189-610da04ec50c
-- title:
--   Marked-Poisson counts on null-intensity overlaps equal counts of disjoint parts at all times almost surely
-- statement:
--   For the original Chapter 6 marked Poisson point process, when two measurable mark sets B and C have zero intensity on their intersection, almost surely and simultaneously for all deterministic observation times, their cumulative counts coincide with counts on disjoint parts B\C and C\B. Use source Poisson zero-intensity count vanishing at every time plus source spatial additive count partition. This removes measure-zero spatial overlap while retaining the original mark and time quantifiers.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.nullIntensityOverlapCountsEqualDisjointPartsAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hNull : n (B ∩ C) = 0) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t B = N omega t (B \ C) ∧
      N omega t C = N omega t (C \ B) := by sorry
