-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_orthogonal_weight_decomp_of_mem_wtNear
-- name    : GlobalTheory.T.exists_orthogonal_weight_decomp_of_mem_wtNear
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:37.143333+00:00
-- url     : https://prove2.me/theorems/73064ad1-f1e9-4118-88d7-f04fc5b58859
-- title:
--   T: exists orthogonal weight decomp of mem wt Near
-- statement:
--   The T construction uses the exists orthogonal weight decomp of mem wt Near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WtNearOrthDecompStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WtNearOrthDecompStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearOrthDecomp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearOrthDecompStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_orthogonal_weight_decomp_of_mem_wtNear : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t ∧ IsWeight E ω (x ω)) ∧ w = ∑ ω ∈ T, x ω ∧ ∀ ω ∈ T, ∀ ω' ∈ T, ω ≠ ω' → ⟪x ω, x ω'⟫_ℂ = 0 := by sorry
