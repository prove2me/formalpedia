-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroAPlusSeparatedOutsideRectanglesPoissonProduct
-- name    : Kyprianou.Ch06.zeroAPlusSeparatedOutsideRectanglesPoissonProduct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:18:11.511475+00:00
-- url     : https://prove2.me/theorems/56283337-cafa-4512-9eae-1ac56796da9b
-- title:
--   Original Poisson product for one A-zero rectangle and any finite compatible outside space-time rectangles
-- statement:
--   From the original Chapter 6 marked-Poisson rectangle law, adjoining a zero-count A rectangle [0,r]×A to any finite family of outside-A rectangles that are pairwise separated by space or nonoverlapping time preserves the exact product of all Poisson atom probabilities. The original finite measurable mark-intensity and rectangle compatibility assumptions are all retained.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroAPlusSeparatedOutsideRectanglesPoissonProduct
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A : Set E) (hA : MeasurableSet A) (hFA : n A < ⊤)
    (m : Nat) (starts stops : Fin m → NNReal)
    (B : Fin m → Set E) (counts : Fin m → Nat)
    (hValid : ∀ i, starts i ≤ stops i ∧
      MeasurableSet (B i) ∧ n (B i) < ⊤)
    (hAB : ∀ i, Disjoint A (B i))
    (hSep : ∀ i j : Fin m, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (B i) (B j))
    (r : NNReal) :
    P {omega | N omega r A - N omega 0 A = 0 ∧
      ∀ i : Fin m, N omega (stops i) (B i) -
        N omega (starts i) (B i) = counts i} =
    ProbabilityTheory.poissonMeasure (r * (n A).toNNReal) {0} *
      ∏ i : Fin m, ProbabilityTheory.poissonMeasure
        ((stops i - starts i) * (n (B i)).toNNReal) {counts i} := by sorry
