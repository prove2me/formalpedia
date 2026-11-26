-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalCrossingCellKernelV1
-- name    : Kyprianou.Ch05.renewalCrossingCellKernelV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:59:56.462147+00:00
-- url     : https://prove2.me/theorems/bad2f9a4-3441-50ac-be27-7d9eb916af39
-- title:
--   Each renewal crossing-index event has the iterated product kernel law
-- statement:
--   Each renewal crossing-index event has the iterated product kernel law
-- source:
--   Kyprianou (2006), Lemma 5.5

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Kyprianou.Ch05

open Classical in
theorem Kyprianou.Ch05.renewalCrossingCellKernelV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : ℕ → Omega → ℝ) (F : Measure ℝ)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x : ℝ) (hx : 0 < x)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA2 : A ⊆ Ioi (0 : ℝ)) (hB2 : B ⊆ Ioc (0 : ℝ) x) (n : ℕ) :
    P {w : Omega | renewalEpoch Z n w ∈ Icc (0 : ℝ) x ∧
      x < renewalEpoch Z n w + Z n w ∧
      Z n w - (x - renewalEpoch Z n w) ∈ A ∧ x - renewalEpoch Z n w ∈ B} = ∫⁻ v in Icc (0 : ℝ) x,
      (∫⁻ z in Ioi (x - v),
        (if z - (x - v) ∈ A ∧ x - v ∈ B then (1 : ENNReal) else 0) ∂F)
      ∂(renewalConvolutionPower F n) := by
  sorry
