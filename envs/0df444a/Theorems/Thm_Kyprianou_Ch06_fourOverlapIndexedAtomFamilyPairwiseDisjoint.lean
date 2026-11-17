-- Prove2me | Theorems.Thm_Kyprianou_Ch06_fourOverlapIndexedAtomFamilyPairwiseDisjoint
-- name    : Kyprianou.Ch06.fourOverlapIndexedAtomFamilyPairwiseDisjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:41:02.743363+00:00
-- url     : https://prove2.me/theorems/b13beddb-59a7-43fa-b796-ffc65b12a99b
-- title:
--   Two distinct indices of the finite four-rectangle overlap atom family represent disjoint events
-- statement:
--   Distinct pairs of overlap atom indices require different exact observed pre-s counts in either B∩C or C\B. Hence the corresponding four-rectangle count-cylinder events are disjoint, including the deterministic invalid-index empty cases. This is a purely algebraic set identity on the original source observation variables.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.fourOverlapIndexedAtomFamilyPairwiseDisjoint
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (N : Omega → NNReal → Set E → Nat)
    (B C : Set E) (s t : NNReal) (k l : Nat) :
    let F : Fin (k+1) × Fin (l+1) → Set Omega := fun i =>
      {omega | (i.1 : Nat)+(i.2 : Nat) ≤ l ∧
        N omega s (B \ C) = k-(i.1 : Nat) ∧
        N omega s (B ∩ C) = (i.1 : Nat) ∧
        N omega s (C \ B) = (i.2 : Nat) ∧
        N omega t C - N omega s C = l-(i.1 : Nat)-(i.2 : Nat)}
    Pairwise (fun i j => Disjoint (F i) (F j)) := by sorry
