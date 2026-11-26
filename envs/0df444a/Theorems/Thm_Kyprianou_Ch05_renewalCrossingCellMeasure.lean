-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalCrossingCellMeasure
-- name    : Kyprianou.Ch05.renewalCrossingCellMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:56:45.374794+00:00
-- url     : https://prove2.me/theorems/76838b9c-e7d9-4bdf-b868-9d48cd7b4ac9
-- title:
--   A single renewal crossing cell has the corresponding double positive integral
-- statement:
--   A single renewal crossing cell has the corresponding double positive integral
-- source:
--   Kyprianou (2006), Lemma 5.5; finite-level renewal crossing and tail integrability.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

open Classical in
theorem Kyprianou.Ch05.renewalCrossingCellMeasure
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x : Real) (A B : Set Real) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA2 : A ⊆ Ioi 0) (n : Nat) :
    P ((fun n : Nat => {w : Omega |
      renewalEpoch Z n w ∈ Icc 0 x ∧
      Z n w - (x-renewalEpoch Z n w) ∈ A ∧
      x-renewalEpoch Z n w ∈ B}) n) =
    ∫⁻ v in Icc (0 : Real) x,
      (∫⁻ z in Ioi (x-v),
        (if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0) ∂F)
      ∂(renewalConvolutionPower F n) := by sorry
