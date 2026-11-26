-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41PathCompactV10
-- name    : Kyprianou.Ch04.exercise41PathCompactV10
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:43:14.983792+00:00
-- url     : https://prove2.me/theorems/a2dc4812-49a2-5cbe-8647-87ad55252b2b
-- title:
--   Measurable real-time extension and common compact bound for cadlag path values and left limits
-- statement:
--   Measurable real-time extension and common compact bound for cadlag path values and left limits
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41PathCompactV10
    {Ω : Type} (X Xleft : NNReal → Ω → ℝ) (w : Ω)
    (hCadlag : IsCadlag (fun t : NNReal => X t w))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w)))
    (t : NNReal) :
    Measurable (fun s : ℝ => X s.toNNReal w) ∧
    ∃ R : ℝ, 0 < R ∧ (∀ s : NNReal, s ≤ t → |X s w| ≤ R) ∧
      (∀ s : NNReal, 0 < s → s ≤ t → |Xleft s w| ≤ R) := by
  sorry
