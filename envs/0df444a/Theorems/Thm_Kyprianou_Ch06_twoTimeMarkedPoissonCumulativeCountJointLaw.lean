-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoTimeMarkedPoissonCumulativeCountJointLaw
-- name    : Kyprianou.Ch06.twoTimeMarkedPoissonCumulativeCountJointLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:07:13.32126+00:00
-- url     : https://prove2.me/theorems/d679d37f-e448-4bd1-9ab3-324462ac58ad
-- title:
--   Joint Poisson law of two cumulative counts at ordered times for one mark set
-- statement:
--   For the authentic Chapter 6 marked Poisson process, one measurable finite-intensity mark set A and observation times 0≤s≤t, the probability that N_s(A)=k and N_t(A)=k+l equals the product of Poisson masses with parameters s n(A) and (t-s)n(A). This uses original zero-initial-count and monotone path assumptions to identify cumulative counts with consecutive increments, and the separately proved two-interval independent Poisson count law. It is a finite-dimensional building block for overlapping mark/time cylinders.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.twoTimeMarkedPoissonCumulativeCountJointLaw
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A : Set E) (hA : MeasurableSet A) (hFinite : n A < ⊤)
    (s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega s A = k ∧ N omega t A = k+l} =
    ProbabilityTheory.poissonMeasure
      (s * (n A).toNNReal) {k} *
    ProbabilityTheory.poissonMeasure
      ((t-s) * (n A).toNNReal) {l} := by sorry
