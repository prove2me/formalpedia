-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unit_leftMulMatrix_of_commute_companion
-- name    : GlobalTheory.T.exists_unit_leftMulMatrix_of_commute_companion
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:50.897572+00:00
-- url     : https://prove2.me/theorems/fdf72acb-f9ad-4d20-9f03-045c93930a19
-- title:
--   T: exists unit left Mul Matrix of commute companion
-- statement:
--   The T construction uses the exists unit left Mul Matrix of commute companion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitLeftMulMatrixOfCommuteCompanionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitLeftMulMatrixOfCommuteCompanionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitLeftMulMatrixOfCommuteCompanion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitLeftMulMatrixOfCommuteCompanionStatement
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

theorem GlobalTheory.T.exists_unit_leftMulMatrix_of_commute_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (t : GL (Fin r) F), (t : Matrix (Fin r) (Fin r) F) * companion p = companion p * (t : Matrix (Fin r) (Fin r) F) → ∃ t₁ : A.Kˣ, LinDesc.tm A hG t₁ = t := by sorry
