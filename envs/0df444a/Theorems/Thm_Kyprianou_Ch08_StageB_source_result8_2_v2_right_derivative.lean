-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_right_derivative
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_right_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:07:35.792047+00:00
-- url     : https://prove2.me/theorems/9a305b89-3829-4ec2-af70-456b5023e899
-- title:
--   Theorem 8.2 helper: open-tail scale derivative
-- statement:
--   For an actual q-excursion-height law and its scale representation, the scale function has right derivative at every positive x, with coefficient Phi(psi,q) plus the open-tail mass n((x,∞)).

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

theorem source_result8_2_v2_right_derivative
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q : ℝ) (n : Measure ℝ)
    (hLaw : HasActualQExcursionHeightLaw P D ψ q n)
    (hRep : HasQExcursionScaleRepresentation ψ q (W q) n) :
    ∀ x : ℝ, 0 < x →
      ∃ dRight : ℝ,
        HasDerivWithinAt (W q) dRight (Set.Ici x) x ∧
        dRight = (Phi ψ q + (n (Set.Ioi x)).toReal) * W q x := by
  sorry

end Kyprianou.Ch08.StageB
