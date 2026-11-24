-- Prove2me | Theorems.Thm_GlobalTheory_exists_isometric_intertwiner_of_matrixCoeff_eq
-- name    : GlobalTheory.exists_isometric_intertwiner_of_matrixCoeff_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:07.929882+00:00
-- url     : https://prove2.me/theorems/9138749c-46c7-4909-8e48-1e60c6994b08
-- title:
--   Global Theory: exists isometric intertwiner of matrix Coeff eq
-- statement:
--   The Global Theory construction uses the exists isometric intertwiner of matrix Coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometricIntertwinerOfMatrixCoeffEq.lean#L18-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometricIntertwinerOfMatrixCoeffEq.lean#L18-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometricIntertwinerOfMatrixCoeffEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.exists_isometric_intertwiner_of_matrixCoeff_eq :
    ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (Hp : Type) [NormedAddCommGroup Hp]
      [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)),
      (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ g x, ‖π g x‖ = ‖x‖) → ∀ (w : H) (v : Hp),
      (∀ y : H, (∀ g, ⟪y, σ g w⟫_ℂ = 0) → y = 0) → (∀ g, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) →
      ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u) := by sorry
