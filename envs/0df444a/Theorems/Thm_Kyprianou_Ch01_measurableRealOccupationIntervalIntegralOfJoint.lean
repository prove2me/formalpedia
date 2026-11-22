-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measurableRealOccupationIntervalIntegralOfJoint
-- name    : Kyprianou.Ch01.measurableRealOccupationIntervalIntegralOfJoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:58:13.054316+00:00
-- url     : https://prove2.me/theorems/033ceefa-7861-4ee6-8bfe-a209fc2e38b2
-- title:
--   Fixed-time Lamperti occupation interval integrals are measurable for jointly measurable integrands
-- statement:
--   Given a real-valued NNReal-indexed jointly measurable stochastic process Z, its real-time occupation interval integral over 0≤s≤t, evaluated at the nonnegative-time coordinate Real.toNNReal s, is a measurable sample-space function for every fixed nonnegative t. Compose joint measurability with the continuous Real.toNNReal time coercion to obtain a measurable function on Ω×ℝ. Apply Mathlib's StronglyMeasurable.integral_prod_right for the restricted volume measure on Ioc 0 t. Convert the restricted Lebesgue integral into the interval integral by intervalIntegral.integral_of_le. This establishes the occupation-clock measurability ingredient in Lamperti's inverse clock without a finite offspring moment or integrability assumption: Bochner integrals are defined as zero when not integrable.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4 inverse occupation clock. Source exact branchingOccupation definition in Definitions.Def_Kyprianou_Ch01_BranchingClocks. Pinned Mathlib signatures StronglyMeasurable.integral_prod_right and intervalIntegral.integral_of_le verified by remote probe 1515b04a-2e00-4c3e-bf6a-9fcbc44ed098. Supports published jointly measurable branching population version theorem 3e5ffb1c-118e-4f86-a96a-376c4f6afad2 and original a50b477a-4a36-47b8-a220-857f6c082b64.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.measurableRealOccupationIntervalIntegralOfJoint
    {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℝ≥0 → Ω → ℝ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => Z z.1 z.2))
    (t : ℝ≥0) :
    Measurable (fun ω : Ω =>
      ∫ s in (0 : ℝ)..(t : ℝ), Z (Real.toNNReal s) ω) := by
  sorry
