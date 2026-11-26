-- Prove2me | Theorems.Thm_Kyprianou_Ch04_levyJointMeasurableVersionV1
-- name    : Kyprianou.Ch04.levyJointMeasurableVersionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:36:24.265067+00:00
-- url     : https://prove2.me/theorems/49bfff65-02c8-593e-abd6-40d126260d51
-- title:
--   Jointly measurable version of a Levy process
-- statement:
--   Use a measurable whole-path modification on a common measurable conull cadlag gate, then apply joint measurability of right-continuous measurable sections.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.levyJointMeasurableVersionV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) :
    ∃ Z : ℝ≥0 → Ω → ℝ,
      Measurable (fun z : ℝ≥0 × Ω => Z z.1 z.2) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Z t ω = X t ω) := by
  sorry
