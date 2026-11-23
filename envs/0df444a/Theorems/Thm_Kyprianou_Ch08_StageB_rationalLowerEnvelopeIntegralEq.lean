-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_rationalLowerEnvelopeIntegralEq
-- name    : Kyprianou.Ch08.StageB.rationalLowerEnvelopeIntegralEq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T10:53:13.504798+00:00
-- url     : https://prove2.me/theorems/746f8225-c5b8-493f-a5ac-787563c0d855
-- title:
--   Lemma 8.2: original null-measurable event integral equals its countable rational lower measurable-envelope integral
-- statement:
--   For a nonnegative or signed real payoff and an increasing family of null-measurable events, a.e. strict-height margins guarantee equality of the original restricted integral and the integral over the countable rational lower measurable envelope. The envelope membership equivalence is explicit. A.e. equality of rational null-measurable representatives, rational density, and integral_indicator/setIntegral_congr_set preserve the original measure and payoff.
-- source:
--   Pinned Mathlib ae_all_iff, NullMeasurableSet.toMeasurable_ae_eq, exists_rat_btwn, setIntegral_congr_set. Direct source-faithful child of connected Kyprianou Chapter 8 Lemma 8.2 measure-theory obligation 23c0e5e8-b9b9-499a-9824-f3e0c6932d16.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem Kyprianou.Ch08.StageB.rationalLowerEnvelopeIntegralEq
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → ℝ) (A B : ℝ → Set Ω)
    (hMeas : ∀ h : ℝ, NullMeasurableSet (A h) P)
    (hMono : Monotone A)
    (hMargin : ∀ y : ℝ, ∀ᵐ ω ∂P,
      g ω ≠ 0 → ω ∈ A y →
        ∃ h : ℝ, h < y ∧ ω ∈ A h)
    (hBMeas : ∀ y : ℝ, MeasurableSet (B y))
    (hBDef : ∀ y : ℝ, ∀ ω : Ω,
      ω ∈ B y ↔
        ∃ r : ℚ, (r : ℝ) < y ∧
          ω ∈ toMeasurable P (A (r : ℝ))) :
    ∀ y : ℝ,
      (∫ ω in B y, g ω ∂P) =
      (∫ ω in A y, g ω ∂P) := by
  sorry
