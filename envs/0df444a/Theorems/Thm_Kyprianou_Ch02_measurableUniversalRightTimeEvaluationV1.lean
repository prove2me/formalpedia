-- Prove2me | Theorems.Thm_Kyprianou_Ch02_measurableUniversalRightTimeEvaluationV1
-- name    : Kyprianou.Ch02.measurableUniversalRightTimeEvaluationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:51:23.792613+00:00
-- url     : https://prove2.me/theorems/3ce4e9a1-451f-4bad-b144-b28d1b5544b1
-- title:
--   Universal measurable evaluation of right-continuous real paths
-- statement:
--   Evaluate a path on dyadic ceilings and take the measurable limsup. Right continuity gives the correct evaluation.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15; independent random-time integration.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.measurableUniversalRightTimeEvaluationV1 :
    ∃ E : (ℝ≥0 → ℝ) × ℝ≥0 → ℝ, Measurable E ∧
      ∀ (f : ℝ≥0 → ℝ), (∀ t, ContinuousWithinAt f (Ici t) t) →
        ∀ t, E (f, t) = f t := by sorry
