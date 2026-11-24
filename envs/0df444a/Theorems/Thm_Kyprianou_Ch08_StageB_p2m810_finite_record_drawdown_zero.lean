-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_finite_record_drawdown_zero
-- name    : Kyprianou.Ch08.StageB.p2m810_finite_record_drawdown_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:44:08.138863+00:00
-- url     : https://prove2.me/theorems/14bd44dd-2f82-4cf8-96ed-2c1e23e1f056
-- title:
--   Finite first record has zero drawdown
-- statement:
--   Every time before the first record has path value at most the crossing level; the value at the record is at least the crossing level. The running maximum therefore equals the current value.
-- source:
--   Kyprianou (2006), Theorem 8.10(i); actual height law of Theorem 8.2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Finite first record has zero drawdown -/
theorem p2m810_finite_record_drawdown_zero :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
      (l : ℝ) (u : ℝ≥0), 0 < l → X 0 ω = 0 →
      BddAbove {z : ℝ | ∃ s : ℝ≥0, s ≤ u ∧ z = X s ω} →
      l ≤ X u ω → tauPlus X l ω = (u : WithTop ℝ≥0) →
      reflectAtSup X 0 u ω = 0 := by
  sorry
end Kyprianou.Ch08.StageB
