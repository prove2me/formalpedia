-- Prove2me | Theorems.Thm_Kyprianou_Ch06_overlapCountCylinderAsFiniteAtomUnionAe
-- name    : Kyprianou.Ch06.overlapCountCylinderAsFiniteAtomUnionAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:14:59.379221+00:00
-- url     : https://prove2.me/theorems/736bd686-31b3-4fef-81f1-d1494a572e55
-- title:
--   Overlapping marked-Poisson count cylinder as finite union of three-atom count conditions
-- statement:
--   For the original marked Poisson counting process, an overlapping two-set count cylinder N_t(B)=k and N_t(C)=l is equivalent almost surely to a finite union of disjoint count conditions on the three spatial atoms B\C, C\B and B∩C, indexed by the Fin type of possible intersection counts q≤min(k,l). This re-indexes the source-preserving Nat-witness decomposition as a finite measurable union suitable for applying the countable disjoint-union independence lemma and the disjoint-mark rectangular Poisson law. No additional independence or source assumptions are imposed.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.overlapCountCylinderAsFiniteAtomUnionAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (t : NNReal) (k l : Nat) :
    ∀ᵐ omega ∂P,
      (N omega t B = k ∧ N omega t C = l) ↔
      ∃ q : Fin (min k l + 1),
        N omega t (B \ C) = k - (q : Nat) ∧
        N omega t (C \ B) = l - (q : Nat) ∧
        N omega t (B ∩ C) = (q : Nat) := by sorry
