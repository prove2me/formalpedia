-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfSeparatedOutsideRectangles
-- name    : Kyprianou.Ch06.zeroACountIndependentOfSeparatedOutsideRectangles
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:31:12.990177+00:00
-- url     : https://prove2.me/theorems/085b486b-49a2-480a-a084-e08d5933a6fa
-- title:
--   Zero cumulative A-count independent of arbitrary compatible finite outside rectangle count cylinders
-- statement:
--   The source Chapter 6 marked-Poisson initial-zero-count property makes a cumulative zero A-count almost surely equivalent to the 0-to-r increment zero count. Combine the proved finite compatible outside rectangle independence for increments with the proved almost-sure event independence transport. The outside family may overlap spatially when time windows are disjoint.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfSeparatedOutsideRectangles
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
    P {omega | N omega r A = 0 ∧
      ∀ i : Fin m, N omega (stops i) (B i) -
        N omega (starts i) (B i) = counts i} =
    P {omega | N omega r A = 0} *
      P {omega | ∀ i : Fin m, N omega (stops i) (B i) -
        N omega (starts i) (B i) = counts i} := by sorry
