-- Prove2me | Theorems.Thm_GlobalTheory_T_residueDegree_eq_inertiaDeg_affine_chart
-- name    : GlobalTheory.T.residueDegree_eq_inertiaDeg_affine_chart
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:37.249618+00:00
-- url     : https://prove2.me/theorems/d7653ab6-35a4-5725-963b-48dbbd6c956e
-- title:
--   T: residue Degree eq inertia Deg affine chart
-- statement:
--   The T construction uses the residue Degree eq inertia Deg affine chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueDegreeEqInertiaDegAffineChartStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueDegreeEqInertiaDegAffineChartStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueDegreeEqInertiaDegAffineChart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueDegreeEqInertiaDegAffineChartStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.residueDegree_eq_inertiaDeg_affine_chart : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by sorry
