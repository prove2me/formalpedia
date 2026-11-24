-- Prove2me | Theorems.Thm_GlobalTheory_spanning_map_factors_through_quotient
-- name    : GlobalTheory.spanning_map_factors_through_quotient
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:39.315541+00:00
-- url     : https://prove2.me/theorems/7f32d6da-b077-466a-bfd3-e30246c63873
-- title:
--   Global Theory: spanning map factors through quotient
-- statement:
--   The Global Theory construction uses the spanning map factors through quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeProjectionFromLattice.lean#L5-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeProjectionFromLattice.lean#L5-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeProjectionFromLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.spanning_map_factors_through_quotient :
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W)
    (F : Submodule ℂ W), Submodule.span ℂ (Set.range P) = ⊤ → Module.finrank ℂ W = 2 * g →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ c : Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ F ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0) →
    ∃ Q : W →ₗ[ℂ] (Fin g → ℂ), LinearMap.ker Q = F ∧ (∀ x, Q (P x) = x) ∧ Module.finrank ℂ F = g := by sorry
