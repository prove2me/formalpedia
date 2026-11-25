-- Prove2me | Theorems.Thm_GlobalTheory_quadForm_le_on_sup
-- name    : GlobalTheory.quadForm_le_on_sup
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:05:14.891121+00:00
-- url     : https://prove2.me/theorems/2afaaa15-8224-437d-b8b8-884b6573a864
-- title:
--   Global Theory: quad Form le on sup
-- statement:
--   The Global Theory construction uses the quad Form le on sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CompactCasimirLeSubspaceMonotone.lean#L21-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CompactCasimirLeSubspaceMonotone.lean#L21-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeSubspaceMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.quadForm_le_on_sup {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] (B : M →ₗ[ℂ] M)
    (hB : B.IsSymmetric) (C : ℝ) (S₁ S₂ : Submodule ℂ M) [FiniteDimensional ℂ S₁] [FiniteDimensional ℂ S₂]
    (h₁ : ∀ x ∈ S₁, B x ∈ S₁) (h₂ : ∀ x ∈ S₂, B x ∈ S₂)
    (b₁ : ∀ x ∈ S₁, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) (b₂ : ∀ x ∈ S₂, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) :
    ∀ x ∈ S₁ ⊔ S₂, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2 := by sorry
