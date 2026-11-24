-- Prove2me | Theorems.Thm_Kyprianou_Ch03_measurableLeftEvaluationOnCadlagV1
-- name    : Kyprianou.Ch03.measurableLeftEvaluationOnCadlagV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T08:06:57.741253+00:00
-- url     : https://prove2.me/theorems/90916305-dd17-4c4e-89d2-3e14aac7fc00
-- title:
--   Measurable deterministic left evaluation on cadlag paths
-- statement:
--   Choose a deterministic sequence tending from the left at every positive time. Its coordinate limsup is measurable and equals the left limit on cadlag paths. At zero use ordinary evaluation.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.4, exact parent 738b23d9-7a4a-4950-8e30-28b1734d73dd and children 42196240-b3a8-4082-98f6-d9e7e4a02b71, 1267c650-c871-460d-b8c1-f7127daafb6e.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.measurableLeftEvaluationOnCadlagV1
    : ∃ L : NNReal → (NNReal → Real) → Real,
      (∀ u, Measurable (L u)) ∧
      ∀ (f : NNReal → Real), IsCadlag f → ∀ u, 0 < u →
        L u f = Function.leftLim f u := by sorry
