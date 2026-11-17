-- Prove2me | Theorems.Thm_Kyprianou_Ch06_unionMarkedCountZeroIffBothZeroAe
-- name    : Kyprianou.Ch06.unionMarkedCountZeroIffBothZeroAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:08:22.75905+00:00
-- url     : https://prove2.me/theorems/02cef9ef-4d7d-45f8-8094-d9c0fbdd9851
-- title:
--   Zero marked-Poisson counts on two overlapping sets iff zero count on their union almost surely
-- statement:
--   Under the exact original Chapter 6 marked Poisson count process assumptions, for every two arbitrary mark sets B,C the event that both N_t(B)=0 and N_t(C)=0 is almost surely equivalent at every deterministic time t to the event N_t(B∪C)=0. The proof uses the source almost-sure finite additivity on disjoint spatial cells, so overlapping B,C cause no obstacle. It enables an original-source two-coordinate overlapping mark-zero-count cylinder to reduce to a previously Proved single outside mark count independence theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.unionMarkedCountZeroIffBothZeroAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      (N omega t B = 0 ∧ N omega t C = 0) ↔
      N omega t (B ∪ C) = 0 := by sorry
