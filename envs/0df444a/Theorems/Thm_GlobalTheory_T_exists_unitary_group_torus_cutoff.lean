-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unitary_group_torus_cutoff
-- name    : GlobalTheory.T.exists_unitary_group_torus_cutoff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:18.439485+00:00
-- url     : https://prove2.me/theorems/945c044b-c4e7-4e98-a084-0a4c67e57331
-- title:
--   T: exists unitary group torus cutoff
-- statement:
--   The T construction uses the exists unitary group torus cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitaryGroupTorusCutoffStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitaryGroupTorusCutoffStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitaryGroupTorusCutoff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitaryGroupTorusCutoffStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_unitary_group_torus_cutoff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p → ∀ (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ Z : Set (Matrix (Fin r) (Fin r) E), IsCompact Z → ∃ α : Matrix.unitaryGroup (Fin r) E → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1 := by sorry
