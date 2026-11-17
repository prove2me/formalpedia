-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfFiniteCompatibleRectangleObservable
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfFiniteCompatibleRectangleObservable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:34:17.724844+00:00
-- url     : https://prove2.me/theorems/31f1696b-c2de-4d5c-9304-096f77a1ab30
-- title:
--   First A-arrival independent of every finite observable generated from compatible outside Poisson rectangles
-- statement:
--   First A-arrival survival is independent of any finite-dimensional count vector reconstructible almost surely as a deterministic function of a finite compatible family of outside-A marked Poisson space-time rectangle counts. The original arbitrary pairwise time-or-space-compatible rectangle source law supplies zero A-count independence; the independently proved source first-arrival continuity transfer supplies the target statement. No extra stochastic assumptions or constraints on observable count levels and dimension.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfFiniteCompatibleRectangleObservable
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (m p : Nat) (starts stops : Fin m → NNReal)
    (B : Fin m → Set E)
    (hValid : ∀ i, starts i ≤ stops i ∧
      MeasurableSet (B i) ∧ n (B i) < ⊤)
    (hAB : ∀ i, Disjoint A (B i))
    (hSep : ∀ i j : Fin m, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (B i) (B j))
    (t : NNReal) (Y : Omega → Fin p → Nat)
    (f : (Fin m → Nat) → Fin p → Nat)
    (hAe : ∀ᵐ omega ∂P,
      Y omega = f (fun i =>
        N omega (stops i) (B i) - N omega (starts i) (B i)))
    (levels : Fin p → Nat) :
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      Y omega = levels} =
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | Y omega = levels} := by sorry
