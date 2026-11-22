-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_atoms_c1
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_atoms_c1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T15:06:17.85033+00:00
-- url     : https://prove2.me/theorems/d5e9acf8-5f4c-4200-afa7-dba2c6f70f07
-- title:
--   Theorem 8.2 helper: derivative equality and atomless C1 criterion
-- statement:
--   Given the actual q-excursion-height law, its scale representation, and the two one-sided derivative formulae required by Theorem 8.2, the derivative formulae agree at x>0 exactly when the excursion-height measure has no atom at x; the scale function is continuously differentiable on (0,∞) exactly when the measure has no positive atoms. This conditional helper packages the final clauses of source_result8_2_v2 for a source-faithful parent proof.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

theorem source_result8_2_v2_atoms_c1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q : ℝ) (n : Measure ℝ)
    (hn : HasActualQExcursionHeightLaw P D ψ q n)
    (hRep : HasQExcursionScaleRepresentation ψ q (W q) n)
    (hDeriv : ∀ x : ℝ, 0 < x →
      ∃ dLeft dRight : ℝ,
        HasDerivWithinAt (W q) dLeft (Set.Iic x) x ∧
        HasDerivWithinAt (W q) dRight (Set.Ici x) x ∧
        dLeft = (Phi ψ q + (n (Set.Ici x)).toReal) * W q x ∧
        dRight = (Phi ψ q + (n (Set.Ioi x)).toReal) * W q x) :
    (∀ x : ℝ, 0 < x →
      ∃ dLeft dRight : ℝ,
        HasDerivWithinAt (W q) dLeft (Set.Iic x) x ∧
        HasDerivWithinAt (W q) dRight (Set.Ici x) x ∧
        dLeft = (Phi ψ q + (n (Set.Ici x)).toReal) * W q x ∧
        dRight = (Phi ψ q + (n (Set.Ioi x)).toReal) * W q x ∧
        (dLeft = dRight ↔ n {x} = 0)) ∧
    (ContDiffOn ℝ 1 (W q) (Set.Ioi (0 : ℝ)) ↔
      ∀ x : ℝ, 0 < x → n {x} = 0) := by
  sorry

end Kyprianou.Ch08.StageB
