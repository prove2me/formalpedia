-- Prove2me | Theorems.Thm_Kyprianou_Ch01_integerRightContinuousGatedJointVersion
-- name    : Kyprianou.Ch01.integerRightContinuousGatedJointVersion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:49:38.99171+00:00
-- url     : https://prove2.me/theorems/f8da87ad-07ae-408c-a47f-fb139deec066
-- title:
--   Jointly measurable integer process version from a measurable all-path right-continuous gate
-- statement:
--   For fixed-time measurable integer process F and a measurable event G on which every sample path F(·,ω) is right-continuous at all times, define W(t,ω)=F(t,ω) on G and zero outside. Every W(t) is globally measurable and every W sample path is right-continuous. Cast W to Real using the continuous ℤ→ℝ map and apply the existing proved AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation. Compose with Int.floor, which recovers W exactly, to prove global joint measurability. On G, W=F simultaneously at all times. This is a deterministic gated-measurability result with no probability law assumptions.
-- source:
--   Kyprianou Chapter 1 §1.3.4 reverse Lamperti, connected through Kyprianou.Ch01.reverseLampertiNonexplosiveJointIntegerProcessVersion UUID 16c022df-d006-4521-8a26-2c3b085468b6. Existing Proved joint evaluation UUID 8aafec11-d8a5-443c-9386-270a0d5c8a04.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.integerRightContinuousGatedJointVersion
    {Ω : Type*} [MeasurableSpace Ω]
    (F : ℝ≥0 → Ω → ℤ)
    (hF : ∀ t : ℝ≥0, Measurable (F t))
    (G : Set Ω) (hG : MeasurableSet G)
    (hRight : ∀ ω ∈ G, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Set.Ici t) t) :
    ∃ W : ℝ≥0 → Ω → ℤ,
      Measurable (fun z : ℝ≥0 × Ω => W z.1 z.2) ∧
      ∀ ω ∈ G, ∀ t : ℝ≥0, W t ω = F t ω := by
  sorry
