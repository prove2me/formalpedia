-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroAIncrementIndependentOfSeparatedOutsideRectangles
-- name    : Kyprianou.Ch06.zeroAIncrementIndependentOfSeparatedOutsideRectangles
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:18:13.988723+00:00
-- url     : https://prove2.me/theorems/272e52a9-8450-4592-8ef1-3c0cc6d724d8
-- title:
--   Zero A-increment count is independent of any finite compatible family of outside space-time rectangle count events
-- statement:
--   The source marked-Poisson finite-rectangle law implies that a zero A-count rectangle is independent of the entire finite count cylinder on any family of outside-A compatible space-time rectangles. The separately published product law for an adjoined A rectangle factors into the original one-rectangle A marginal and the original independent rectangle family product. Outside marks may overlap if their time intervals are disjoint, exactly as allowed by the original source axiom.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroAIncrementIndependentOfSeparatedOutsideRectangles
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
    P {omega | N omega r A - N omega 0 A = 0} *
      P {omega | ∀ i : Fin m, N omega (stops i) (B i) -
        N omega (starts i) (B i) = counts i} := by sorry
