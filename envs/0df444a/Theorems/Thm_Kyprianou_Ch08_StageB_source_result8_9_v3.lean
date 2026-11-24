-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_9_v3
-- name    : Kyprianou.Ch08.StageB.source_result8_9_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:15:35.106298+00:00
-- url     : https://prove2.me/theorems/187462f1-7ddf-402e-8f78-fa61aba5d226
-- title:
--   Theorem 8.9: corrected unrestricted potential kernel
-- statement:
--   Source-equivalent Theorem 8.9 with the correct destination-minus-origin displacement, retaining all hypotheses and differentiability and resolvent conclusions.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.9. Correct the sign of the displacement to y - x; the existing density definition is retained. Supersedes ac87340c-1ef1-4c40-a648-ffcee2754928.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Corrected source result 8.9: displacement is destination minus origin. -/
theorem source_result8_9_v3 :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x : ℝ), 0 < q →
        DifferentiableAt ℝ (Phi ψ) q ∧
        ∃ U : Measure ℝ,
          IsResolvent P (shifted D.X x) q U ∧
          U = volume.withDensity
            (fun y : ℝ =>
              ENNReal.ofReal
                (unrestrictedPotentialDensity ψ q (W q) (y-x))) := by
  sorry

end Kyprianou.Ch08.StageB
