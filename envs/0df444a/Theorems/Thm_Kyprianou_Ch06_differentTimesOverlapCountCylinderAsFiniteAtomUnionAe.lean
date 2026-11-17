-- Prove2me | Theorems.Thm_Kyprianou_Ch06_differentTimesOverlapCountCylinderAsFiniteAtomUnionAe
-- name    : Kyprianou.Ch06.differentTimesOverlapCountCylinderAsFiniteAtomUnionAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:31:11.643032+00:00
-- url     : https://prove2.me/theorems/c6a469bb-e6e4-4771-b191-3bfe0d7a9417
-- title:
--   Overlapping two-mark count cylinder at ordered unequal times as a finite union of four rectangle-atom cylinders
-- statement:
--   For arbitrary possibly overlapping outside mark sets B,C, ordered times s≤t and count levels k,l, partition the cylinder N_s(B)=k and N_t(C)=l almost surely into finite disjoint atoms indexed by common pre-s count q and C-only pre-s count z, with the four rectangle counts on B\C, B∩C, C\B through time s and C on (s,t]. This is source-equivalent and uses only original spatial additivity and monotonicity.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.differentTimesOverlapCountCylinderAsFiniteAtomUnionAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (s t : NNReal) (hst : s ≤ t)
    (k l : Nat) :
    let F : (Fin (k+1) × Fin (l+1)) → Set Omega :=
      fun i => {omega |
        (i.1 : Nat) + (i.2 : Nat) ≤ l ∧
        N omega s (B \ C) = k-(i.1 : Nat) ∧
        N omega s (B ∩ C) = (i.1 : Nat) ∧
        N omega s (C \ B) = (i.2 : Nat) ∧
        N omega t C - N omega s C =
          l-(i.1 : Nat)-(i.2 : Nat)}
    ∀ᵐ omega ∂P,
      (N omega s B = k ∧ N omega t C = l) ↔
      omega ∈ ⋃ i, F i := by sorry
