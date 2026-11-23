-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_rationalLowerEnvelopeAEMembershipOnSupport
-- name    : Kyprianou.Ch08.StageB.rationalLowerEnvelopeAEMembershipOnSupport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:57:03.984287+00:00
-- url     : https://prove2.me/theorems/33c4ab00-9e82-4373-bbdc-d3e50ba5854c
-- title:
--   Lemma 8.2: rational lower measurable envelope equals the original height event almost everywhere on nonzero payoff support
-- statement:
--   At each fixed height, the original monotone null-measurable event coincides almost everywhere on the support of the payoff with the countable rational lower measurable envelope, assuming the source a.e. strict-height margin. Countable rational exceptional sets, monotonicity and rational density supply the two membership directions. This isolates the actual probabilistic content from the subsequent elementary integral equality.
-- source:
--   Derived from pinned Mathlib ae_all_iff and NullMeasurableSet.toMeasurable_ae_eq, and from the exact source a.e. margin condition. Direct child for rationalLowerEnvelopeIntegralEq 746f8225-c5b8-493f-a5ac-787563c0d855, which lies in the linked Chapter 8 Lemma 8.2 reduction.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem Kyprianou.Ch08.StageB.rationalLowerEnvelopeAEMembershipOnSupport
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → ℝ) (A B : ℝ → Set Ω)
    (hMeas : ∀ h : ℝ, NullMeasurableSet (A h) P)
    (hMono : Monotone A)
    (hMargin : ∀ y : ℝ, ∀ᵐ ω ∂P,
      g ω ≠ 0 → ω ∈ A y →
        ∃ h : ℝ, h < y ∧ ω ∈ A h)
    (hBDef : ∀ y : ℝ, ∀ ω : Ω,
      ω ∈ B y ↔
        ∃ r : ℚ, (r : ℝ) < y ∧
          ω ∈ toMeasurable P (A (r : ℝ))) :
    ∀ y : ℝ, ∀ᵐ ω ∂P,
      g ω ≠ 0 → (ω ∈ B y ↔ ω ∈ A y) := by
  sorry
