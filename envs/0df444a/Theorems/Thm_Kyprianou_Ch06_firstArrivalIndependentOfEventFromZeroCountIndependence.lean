-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfEventFromZeroCountIndependence
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfEventFromZeroCountIndependence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:05:29.115955+00:00
-- url     : https://prove2.me/theorems/62f446c4-5baf-4f5a-96bf-cd3ed3595cd6
-- title:
--   Transfer arbitrary-event zero A-count independence to first A-arrival survival independence
-- statement:
--   For a marked Poisson point process with original Chapter 6 first-mark convention and finite A-intensity, independence of a fixed event D from the zero A-count event at every deterministic time implies independence of D from the first A-arrival survival event at any time. Derive continuity of the zero-count joint probability from its exponential Poisson marginal, use the separately proved source first-arrival joint-event continuity sandwich, and substitute the proven first-arrival survival law. No extra measurability, independence or point-process assumptions are added.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfEventFromZeroCountIndependence
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
    (D : Set Omega)
    (hJoint : ∀ s : NNReal,
      P ({omega | N omega s A = 0} ∩ D) =
      P {omega | N omega s A = 0} * P D)
    (t : NNReal) :
    P ({omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} ∩ D) =
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} * P D := by sorry
