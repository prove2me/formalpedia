-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_rationalLowerMeasurableEnvelopeExists
-- name    : Kyprianou.Ch08.StageB.rationalLowerMeasurableEnvelopeExists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:53:08.636704+00:00
-- url     : https://prove2.me/theorems/f54d119e-7ad0-4443-822a-f4511a5a2079
-- title:
--   Lemma 8.2: countable rational lower measurable envelope exists with monotonicity and strict-height margin
-- statement:
--   For any real-parameter family of events on a measure space, a canonical countable union of measurable envelopes at lower rational thresholds is a measurable, monotone family. Every member of its event at a threshold belongs to its event at a strictly smaller real threshold. Retain the exact rational-envelope membership characterisation for subsequent integration. This gives a reusable deterministic countable reduction for excursion height laws.
-- source:
--   Exact pinned Mathlib rational-density and toMeasurable lemmas. Child of the connected Kyprianou Chapter 8 Lemma 8.2 measure-theoretic obligation 23c0e5e8-b9b9-499a-9824-f3e0c6932d16, splitting the 122-line direct proof that Prove2Me rejected for size.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem Kyprianou.Ch08.StageB.rationalLowerMeasurableEnvelopeExists
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ℝ → Set Ω) :
    ∃ B : ℝ → Set Ω,
      (∀ y : ℝ, MeasurableSet (B y)) ∧
      Monotone B ∧
      (∀ y : ℝ, ∀ ω : Ω, ω ∈ B y →
        ∃ h : ℝ, h < y ∧ ω ∈ B h) ∧
      (∀ y : ℝ, ∀ ω : Ω,
        ω ∈ B y ↔
          ∃ r : ℚ, (r : ℝ) < y ∧
            ω ∈ toMeasurable P (A (r : ℝ))) := by
  sorry
