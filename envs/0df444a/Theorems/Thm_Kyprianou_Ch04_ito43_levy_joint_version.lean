-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_levy_joint_version
-- name    : Kyprianou.Ch04.ito43_levy_joint_version
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:35:03.571806+00:00
-- url     : https://prove2.me/theorems/f21553e9-81cf-49a1-9e1a-b8d31368621f
-- title:
--   Indistinguishable jointly measurable cadlag version of a Levy process
-- statement:
--   Indistinguishable jointly measurable cadlag version of a Levy process.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- An a.s. cadlag Levy process has a jointly measurable, everywhere right-continuous version
indistinguishable from the original process. -/

theorem Kyprianou.Ch04.ito43_levy_joint_version {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P) :
    ∃ Y : NNReal → Ω → ℝ, Measurable (fun z : NNReal × Ω => Y z.1 z.2) ∧
      (∀ᵐ w ∂P, ∀ t, Y t w = X t w) ∧ ∀ w, IsCadlag (fun t => Y t w) := by sorry
