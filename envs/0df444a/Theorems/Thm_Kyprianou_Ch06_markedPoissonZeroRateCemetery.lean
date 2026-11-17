-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonZeroRateCemetery
-- name    : Kyprianou.Ch06.markedPoissonZeroRateCemetery
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:41:49.159496+00:00
-- url     : https://prove2.me/theorems/e5ac543a-6e97-49a9-aa51-53cbd1019951
-- title:
--   Lemma 6.18 atomic obligation: markedPoissonZeroRateCemetery
-- statement:
--   A separately provable source-exact portion of Chapter 6 Lemma 6.18, retaining its entire original marked Poisson model, event definitions and hypotheses.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.markedPoissonZeroRateCemetery
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
    (n A = 0 →
      P {omega | sigma omega = ⊤ ∧ firstMark omega = none} = 1) := by sorry
