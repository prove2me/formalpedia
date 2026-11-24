-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_strict_record_prebound
-- name    : Kyprianou.Ch08.StageB.p2m810_strict_record_prebound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:44:04.569507+00:00
-- url     : https://prove2.me/theorems/62186392-412d-4b82-bea2-d7e31612ca89
-- title:
--   Strict crossing later than a finite record iff the pre-record height is bounded
-- statement:
--   If no strict crossing occurred before the record, the pre-record height is bounded. Conversely, the bound and right continuity at a strictly sub-barrier record give a right neighbourhood with no crossing.
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
/-- Strict crossing later than a finite record iff the pre-record height is bounded -/
theorem p2m810_strict_record_prebound :
    ∀ (f : ℝ≥0 → ℝ) (a : ℝ) (u : ℝ≥0),
      f 0 ≤ a → f u < a → ContinuousWithinAt f (Ici u) u →
      ((u : WithTop ℝ≥0) < tauPlus (fun t (_ : Unit) => f t) a ()) ↔
      (∀ t : ℝ≥0, t < u → f t ≤ a) := by
  sorry
end Kyprianou.Ch08.StageB
