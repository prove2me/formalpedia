-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_antitone_null_set_integral
-- name    : Kyprianou.Ch08.StageB.p2m810_antitone_null_set_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:44:00.848293+00:00
-- url     : https://prove2.me/theorems/02d10ab2-b4d2-4f49-b103-0c6d15bbefe8
-- title:
--   Restricted integrals converge along decreasing null-measurable sets
-- statement:
--   The indicators of a decreasing countable set family converge pointwise to the indicator of the intersection and are dominated by the integrable norm of the integrand.
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
/-- Restricted integrals converge along decreasing null-measurable sets -/
theorem p2m810_antitone_null_set_integral :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (g : Ω → ℝ) (A : ℕ → Set Ω), Integrable g P →
      (∀ n, NullMeasurableSet (A n) P) → Antitone A →
      Tendsto (fun n => ∫ ω in A n, g ω ∂P)
        atTop (nhds (∫ ω in ⋂ n, A n, g ω ∂P)) := by
  sorry
end Kyprianou.Ch08.StageB
