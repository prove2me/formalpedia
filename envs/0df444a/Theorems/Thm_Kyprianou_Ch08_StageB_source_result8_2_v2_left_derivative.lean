-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_left_derivative
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_left_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:06:22.193+00:00
-- url     : https://prove2.me/theorems/1c582dd7-8f01-4c8d-9859-46ba6f80fd22
-- title:
--   Theorem 8.2 helper: closed-tail scale derivative
-- statement:
--   For an actual q-excursion-height law and its scale representation, the scale function has left derivative at every positive x, with coefficient Phi(psi,q) plus the closed-tail mass n([x,∞)).

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

theorem source_result8_2_v2_left_derivative
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q : ℝ) (n : Measure ℝ)
    (hLaw : HasActualQExcursionHeightLaw P D ψ q n)
    (hRep : HasQExcursionScaleRepresentation ψ q (W q) n) :
    ∀ x : ℝ, 0 < x →
      ∃ dLeft : ℝ,
        HasDerivWithinAt (W q) dLeft (Set.Iic x) x ∧
        dLeft = (Phi ψ q + (n (Set.Ici x)).toReal) * W q x := by
  sorry

end Kyprianou.Ch08.StageB
