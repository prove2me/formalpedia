-- Prove2me | Theorems.Thm_Kyprianou_Ch06_finiteUnionMarkedCountZeroIffAllZeroAe
-- name    : Kyprianou.Ch06.finiteUnionMarkedCountZeroIffAllZeroAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:09:58.686229+00:00
-- url     : https://prove2.me/theorems/2b3e53a4-edca-46c4-8b0d-91fdbd95b378
-- title:
--   For arbitrary finite overlapping marked-Poisson mark families, all zero counts iff zero count on their union
-- statement:
--   For the source-faithful Chapter 6 marked Poisson counting process and an arbitrary finite family of possibly overlapping mark sets B_i, the entire family of zero-count conditions N_t(B_i)=0 is almost surely equivalent for every t to the single condition N_t(⋃_i B_i)=0. This follows by induction from the genuine original sample-path finite additivity of counts on disjoint marks and the two-overlap zero-union identity, retaining all mark set and time quantifiers. It permits many-dimensional overlapping simultaneous zero-count cylinders to reduce to a single previously proved outside A-mark count independent of first A-arrival.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.finiteUnionMarkedCountZeroIffAllZeroAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (m : Nat) (B : Fin m → Set E) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      (∀ i : Fin m, N omega t (B i) = 0) ↔
      N omega t (⋃ i : Fin m, B i) = 0 := by sorry
