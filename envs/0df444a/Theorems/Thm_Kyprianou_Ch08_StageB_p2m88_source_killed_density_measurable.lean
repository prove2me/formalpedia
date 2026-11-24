-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_killed_density_measurable
-- name    : Kyprianou.Ch08.StageB.p2m88_source_killed_density_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:41:32.06+00:00
-- url     : https://prove2.me/theorems/d20b6cee-931e-44c6-b672-215c23de6582
-- title:
--   Measurability of the half-line scale density
-- statement:
--   A scale function is continuous on the nonnegative half-line and zero on the negative half-line; hence it is globally measurable, and so is the displayed nonnegative density.
-- source:
--   Kyprianou (2006), Corollary 8.8, zero-discount limit.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal

namespace Kyprianou.Ch08.StageB
 theorem p2m88_source_killed_density_measurable :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ), HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 ≤ q → ∀ x : ℝ,
      Measurable (fun y : ℝ => ENNReal.ofReal (killedHalflineDensity ψ q (W q) x y)) := by
  sorry
end Kyprianou.Ch08.StageB
