-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measurableJointInverseReciprocalOccupationFromSections
-- name    : Kyprianou.Ch01.measurableJointInverseReciprocalOccupationFromSections
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T15:47:52.895801+00:00
-- url     : https://prove2.me/theorems/6d5a9c3e-53fc-4c4e-a9ee-3857ad86cc4b
-- title:
--   Joint measurable inverse reciprocal-occupation clock from measurable occupation sections
-- statement:
--   If each physical-clock occupation section is measurable in the path variable, the rational-infimum formula gives a jointly measurable inverse occupation clock in (time, path).
-- source:
--   Kyprianou 2006 Section 1.3.4; exact product-space extension of Proved Kyprianou.Ch01.measurableInverseReciprocalOccupationFromSections and Proved inverseReciprocalOccupationRationalInf.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.measurableJointInverseReciprocalOccupationFromSections
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hMeas : ∀ s : ℝ≥0,
      Measurable (fun ω : Ω => reciprocalOccupation X s ω)) :
    Measurable (fun z : ℝ≥0 × Ω =>
      inverseReciprocalOccupation X z.1 z.2) := by
  sorry
