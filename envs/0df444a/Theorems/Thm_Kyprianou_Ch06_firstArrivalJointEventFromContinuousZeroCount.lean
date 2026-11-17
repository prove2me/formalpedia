-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
-- name    : Kyprianou.Ch06.firstArrivalJointEventFromContinuousZeroCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:16:38.855172+00:00
-- url     : https://prove2.me/theorems/7ace224a-58c2-4580-ac19-64940c1afbff
-- title:
--   Chapter 6 first-arrival event: exact joint survival via continuous zero-count probability
-- statement:
--   Given an almost-surely monotone mark-count process with zero initial count, and an arbitrary auxiliary sample event C, if the joint zero-count probability P[N_s(A)=0 and C] is right-continuous at time t then its value equals the joint probability P[first positive A-count occurs strictly after t and C]. This source-faithful first-arrival sandwich step avoids assuming measurability of the first-arrival selector, and is a key nontrivial step towards the finite-dimensional outside-mark independence clause of Lemma 6.18.

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalJointEventFromContinuousZeroCount
    {Omega E : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (C : Set Omega) (t : NNReal)
    (hInit : ∀ᵐ omega ∂P, N omega 0 A = 0)
    (hMono : ∀ᵐ omega ∂P,
      Monotone (fun s : NNReal => N omega s A))
    (hCont : ContinuousAt
      (fun s : NNReal => P {omega | N omega s A = 0 ∧ omega ∈ C}) t) :
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A}) ∧
      omega ∈ C} =
    P {omega | N omega t A = 0 ∧ omega ∈ C} := by sorry
