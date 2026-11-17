-- Prove2me | Theorems.Thm_Kyprianou_Ch06_disjointOutsideCountVectorRectangleRepresentation
-- name    : Kyprianou.Ch06.disjointOutsideCountVectorRectangleRepresentation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T05:56:04.522428+00:00
-- url     : https://prove2.me/theorems/e2870779-aa0b-4620-95a6-abd6f05fb041
-- title:
--   Lemma 6.18 compatible rectangle representation for pairwise-disjoint outside mark sets
-- statement:
--   Whenever the finite outside-A mark observation sets are pairwise disjoint, their count vector is immediately represented by compatible rectangles [0,t_i]×B_i. The marked Poisson process gives N_0(B_i)=0 almost surely, so the rectangle increments are exactly the original counts. This handles the disjoint case of the new general finite rectangle representation child.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, disjoint-mark case of finite cylinder reconstruction.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.disjointOutsideCountVectorRectangleRepresentation
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (m : Nat) (times : Fin m → NNReal) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤)
    (hDisjoint : ∀ i j : Fin m, i ≠ j → Disjoint (B i) (B j)) :
    ∃ (k : Nat) (starts stops : Fin k → NNReal)
      (D : Fin k → Set E),
      (∀ i, starts i ≤ stops i ∧ MeasurableSet (D i) ∧ n (D i) < ⊤) ∧
      (∀ i, Disjoint A (D i)) ∧
      (∀ i j : Fin k, i ≠ j →
        stops i ≤ starts j ∨ stops j ≤ starts i ∨
          Disjoint (D i) (D j)) ∧
      ∃ f : (Fin k → Nat) → Fin m → Nat,
        ∀ᵐ omega ∂P,
          (fun i : Fin m => N omega (times i) (B i)) =
            f (fun i : Fin k =>
              N omega (stops i) (D i) - N omega (starts i) (D i)) := by sorry
