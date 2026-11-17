-- Prove2me | Theorems.Thm_Kyprianou_Ch06_overlapCountCylinderAsDisjointAtomSumAe
-- name    : Kyprianou.Ch06.overlapCountCylinderAsDisjointAtomSumAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:10:27.312396+00:00
-- url     : https://prove2.me/theorems/f1e1f4d3-c6cb-4ca5-9145-14d5889d46b1
-- title:
--   Chapter 6 overlapping count cylinder decomposes into finite disjoint spatial atoms
-- statement:
--   The original marked Poisson counting process has almost-sure spatial finite additivity. Two possibly overlapping mark-count conditions N_t(B)=k and N_t(C)=l at a common observation time are equivalent almost surely to a finite disjoint union over possible intersection counts q≤min(k,l) where the disjoint spatial atoms B\C, C\B and B∩C have counts k-q, l-q and q respectively. This exposes a finite-atomic partition suitable for proving independence from counts of an external disjoint mark set without introducing independence assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.overlapCountCylinderAsDisjointAtomSumAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (t : NNReal) (k l : Nat) :
    ∀ᵐ omega ∂P,
      (N omega t B = k ∧ N omega t C = l) ↔
      ∃ q : Nat, q ≤ min k l ∧
        N omega t (B \ C) = k - q ∧
        N omega t (C \ B) = l - q ∧
        N omega t (B ∩ C) = q := by sorry
