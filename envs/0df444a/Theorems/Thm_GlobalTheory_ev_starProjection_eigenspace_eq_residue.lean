-- Prove2me | Theorems.Thm_GlobalTheory_ev_starProjection_eigenspace_eq_residue
-- name    : GlobalTheory.ev_starProjection_eigenspace_eq_residue
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:31:51.099714+00:00
-- url     : https://prove2.me/theorems/a4a0f1fc-42f4-4817-b7f1-0c8720902c44
-- title:
--   Global Theory: ev star Projection eigenspace eq residue
-- statement:
--   The Global Theory construction uses the ev star Projection eigenspace eq residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi.lean#L9-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi.lean#L9-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
open Module

theorem GlobalTheory.ev_starProjection_eigenspace_eq_residue :
    ∀ (Y : Type) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (t : ℕ) (m : Fin t → ℂ) (s : ℂ) (Om : Module.End ℂ Y) (ev : Y →ₗ[ℂ] V) (K : ℂ → (Y →ₗ[ℂ] V)) (q : ℂ → ℂ) (y : Y) (v : V) (l : Fin t), Function.Injective m → Om.IsSymmetric → (∀ (lam : ℂ) (x : Y), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + s) → (∀ (u : ℂ) (x : Y), K u ((u - s) • x + Om x) = (∏ j, (u + m j)) • ev x) → Continuous q → (∀ u, K u y = q u • v) → ev ((Module.End.eigenspace Om (m l + s)).starProjection y) = (q (-m l) / ∏ j ∈ Finset.univ.erase l, (m j - m l)) • v := by sorry
