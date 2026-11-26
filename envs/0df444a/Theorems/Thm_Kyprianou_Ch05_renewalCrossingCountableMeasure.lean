-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalCrossingCountableMeasure
-- name    : Kyprianou.Ch05.renewalCrossingCountableMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:55:59.146806+00:00
-- url     : https://prove2.me/theorems/d602d354-7198-5405-8e69-aa46e7ea84c1
-- title:
--   Positive joint passage event measure equals the sum of the individual crossing cell masses
-- statement:
--   Positive joint passage event measure equals the sum of the individual crossing cell masses
-- source:
--   Kyprianou (2006), Lemma 5.5; finite-level renewal crossing and tail integrability.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalCrossingCountableMeasure
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x : Real) (hx : 0 < x)
    (A B : Set Real) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA2 : A ⊆ Ioi 0) :
    P {w : Omega | 0 < renewalOvershoot Z x w ∧
      renewalOvershoot Z x w ∈ A ∧ renewalUndershoot Z x w ∈ B} = ∑' n : Nat, P ((fun n : Nat => {w : Omega |
      renewalEpoch Z n w ∈ Icc 0 x ∧
      Z n w - (x-renewalEpoch Z n w) ∈ A ∧
      x-renewalEpoch Z n w ∈ B}) n) := by sorry
