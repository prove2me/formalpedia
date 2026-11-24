-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_occupation_sections_measurable
-- name    : Kyprianou.Ch08.StageB.p2m88_source_occupation_sections_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:39:33.773498+00:00
-- url     : https://prove2.me/theorems/f8ff2af8-c0df-4406-9c4e-4813a0ae89b9
-- title:
--   Measurability of source killed occupation time sections
-- statement:
--   Transfer the source path to the almost-surely equal Avram version and use its already proved measurable time-section probabilities.
-- source:
--   Kyprianou (2006), Corollary 8.8, q decreasing to zero.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal

namespace Kyprianou.Ch08.StageB
 theorem p2m88_source_occupation_sections_measurable :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      ∀ x : ℝ, 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
      Measurable (fun t : ℝ≥0 =>
        P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
          shifted D.X x t ω ∈ A}) := by
  sorry
end Kyprianou.Ch08.StageB
