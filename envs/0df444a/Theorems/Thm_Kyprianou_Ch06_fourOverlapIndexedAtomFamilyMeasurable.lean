-- Prove2me | Theorems.Thm_Kyprianou_Ch06_fourOverlapIndexedAtomFamilyMeasurable
-- name    : Kyprianou.Ch06.fourOverlapIndexedAtomFamilyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:41:09.512531+00:00
-- url     : https://prove2.me/theorems/b6937da4-5c4f-4729-890e-cb1761bf7dd6
-- title:
--   Every indexed four-rectangle event in a two-overlap time-split count decomposition is measurable
-- statement:
--   The original marked-Poisson definition requires measurable count maps on measurable mark sets. The four components of a finite overlap atom cylinder are measurable cumulative counts on B\C, B∩C and C\B, and a measurable difference of C-counts at two times. The deterministic index admissibility condition also defines a measurable event. The full atom family is measurable without strengthening the original source point-process assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.fourOverlapIndexedAtomFamilyMeasurable
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (s t : NNReal) (k l : Nat) :
    let F : Fin (k+1) × Fin (l+1) → Set Omega := fun i =>
      {omega | (i.1 : Nat)+(i.2 : Nat) ≤ l ∧
        N omega s (B \ C) = k-(i.1 : Nat) ∧
        N omega s (B ∩ C) = (i.1 : Nat) ∧
        N omega s (C \ B) = (i.2 : Nat) ∧
        N omega t C - N omega s C = l-(i.1 : Nat)-(i.2 : Nat)}
    ∀ i, MeasurableSet (F i) := by sorry
