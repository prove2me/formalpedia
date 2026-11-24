-- Prove2me | Theorems.Thm_GlobalTheory_ResidueDegreeChart_residueDegree_eq_inertiaDeg
-- name    : GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:21:05.066828+00:00
-- url     : https://prove2.me/theorems/a8d648f1-641c-4a84-a86d-12878544b0ac
-- title:
--   Residue Degree Chart: residue Degree eq inertia Deg
-- statement:
--   The Residue Degree Chart construction uses the residue Degree eq inertia Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueDegreeEqInertiaDegAffineChart.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueDegreeEqInertiaDegAffineChart.lean#L66-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueDegreeEqInertiaDegAffineChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ResidueDegreeChart

theorem GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by sorry
