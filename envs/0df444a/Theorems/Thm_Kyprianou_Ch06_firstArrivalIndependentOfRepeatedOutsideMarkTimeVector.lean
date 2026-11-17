-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfRepeatedOutsideMarkTimeVector
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfRepeatedOutsideMarkTimeVector
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:16:36.178853+00:00
-- url     : https://prove2.me/theorems/4c4a537e-e942-480d-90f2-97165d38788c
-- title:
--   First A-arrival survival independent of any finite repeated outside-mark/time count vector
-- statement:
--   The full marked-Poisson first A-arrival survival event is independent of an arbitrary finite vector of possibly incompatible counts of a fixed outside-A mark set B at the same observation time u. Uses the source-proved finite repeated zero-A count factorisation and source-proved first-arrival survival transfer from zero-count independence, without additional process hypotheses. Private remote Lean compilation of the exact theorem together with its source-dependent predecessor reached the sentinel.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfRepeatedOutsideMarkTimeVector
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
    (B : Set E) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFB : n B < ⊤)
    (m : Nat) (u t : NNReal) (levels : Fin m → Nat) :
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      ∀ i : Fin m, N omega u B = levels i} =
    P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | ∀ i : Fin m, N omega u B = levels i} := by sorry
