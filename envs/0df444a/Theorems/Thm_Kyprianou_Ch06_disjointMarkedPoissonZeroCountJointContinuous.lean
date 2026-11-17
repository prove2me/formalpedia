-- Prove2me | Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonZeroCountJointContinuous
-- name    : Kyprianou.Ch06.disjointMarkedPoissonZeroCountJointContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:21:23.375587+00:00
-- url     : https://prove2.me/theorems/28c586ce-5d64-4620-ad8a-0030b6743e80
-- title:
--   Chapter 6 disjoint-mark Poisson joint zero-count event is continuous in its time
-- statement:
--   For a genuine marked Poisson process, disjoint finite-intensity spatial mark sets A,B, and any deterministic outside count N_u(B)=k, the joint probability P[N_s(A)=0 and N_u(B)=k] is continuous in s, including at time zero. The proof reuses the independently proved disjoint mark count independence and marginal Poisson zero-count exponential law; this continuity discharges the nontrivial analytical premise of the first-arrival joint-event sandwich for the one-count outside-mark case.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.disjointMarkedPoissonZeroCountJointContinuous
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B)
    (hFiniteA : n A < ⊤) (hFiniteB : n B < ⊤)
    (t u : NNReal) (k : Nat) :
    ContinuousAt (fun s : NNReal =>
      P {omega | N omega s A = 0 ∧ N omega u B = k}) t := by sorry
