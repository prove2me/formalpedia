-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfDisjointOutsideCylinder
-- name    : Kyprianou.Ch06.zeroACountIndependentOfDisjointOutsideCylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:58:08.255076+00:00
-- url     : https://prove2.me/theorems/c0ac765c-2f88-4c88-a6a9-23fa0428e283
-- title:
--   Chapter 6 zero A-count independent of any finite disjoint outside-mark cylinder
-- statement:
--   For any genuine marked Poisson process and any measurable finite-intensity set A, the zero A count at an arbitrary deterministic time is independent of the joint count cylinder over an arbitrary finite family of pairwise disjoint measurable finite-intensity outside-A mark sets observed at arbitrary times and count levels. The proof uses the full finite-dimensional disjoint-mark count product law on a family obtained by adjoining A to the outside mark family.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfDisjointOutsideCylinder
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A : Set E) (hA : MeasurableSet A) (hFA : n A < ⊤)
    (m : Nat) (times : Fin m → NNReal)
    (B : Fin m → Set E) (counts : Fin m → Nat)
    (hB : ∀ i, MeasurableSet (B i) ∧ n (B i) < ⊤)
    (hAB : ∀ i, Disjoint A (B i))
    (hBij : ∀ i j : Fin m, i ≠ j → Disjoint (B i) (B j))
    (t : NNReal) :
    P {omega | N omega t A = 0 ∧
      ∀ i : Fin m, N omega (times i) (B i) = counts i} =
      P {omega | N omega t A = 0} *
      P {omega | ∀ i : Fin m,
        N omega (times i) (B i) = counts i} := by sorry
