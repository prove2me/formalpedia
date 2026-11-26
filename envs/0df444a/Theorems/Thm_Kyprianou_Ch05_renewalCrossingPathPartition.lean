-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalCrossingPathPartition
-- name    : Kyprianou.Ch05.renewalCrossingPathPartition
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:55:45.614401+00:00
-- url     : https://prove2.me/theorems/3b8ba128-c3d2-500f-b5d7-77fd968c8eb9
-- title:
--   On a nonnegative spacing path positive overshoot selects a unique crossing cell
-- statement:
--   On a nonnegative spacing path positive overshoot selects a unique crossing cell
-- source:
--   Kyprianou (2006), Lemma 5.5; finite-level renewal crossing and tail integrability.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalCrossingPathPartition
    {Omega : Type} (Z : Nat → Omega → Real)
    (w : Omega) (hZ : ∀ n : Nat, 0 ≤ Z n w)
    (hmono : Monotone (fun n : Nat => renewalEpoch Z n w))
    (x : Real) (hx : 0 < x)
    (A B : Set Real) (hA : A ⊆ Ioi 0) :
    (w ∈ {w : Omega | 0 < renewalOvershoot Z x w ∧
      renewalOvershoot Z x w ∈ A ∧ renewalUndershoot Z x w ∈ B} ↔ ∃ n : Nat, w ∈ (fun n : Nat => {w : Omega |
      renewalEpoch Z n w ∈ Icc 0 x ∧
      Z n w - (x-renewalEpoch Z n w) ∈ A ∧
      x-renewalEpoch Z n w ∈ B}) n) ∧
    (∀ i j : Nat, w ∈ (fun n : Nat => {w : Omega |
      renewalEpoch Z n w ∈ Icc 0 x ∧
      Z n w - (x-renewalEpoch Z n w) ∈ A ∧
      x-renewalEpoch Z n w ∈ B}) i → w ∈ (fun n : Nat => {w : Omega |
      renewalEpoch Z n w ∈ Icc 0 x ∧
      Z n w - (x-renewalEpoch Z n w) ∈ A ∧
      x-renewalEpoch Z n w ∈ B}) j → i = j) := by sorry
