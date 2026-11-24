-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_representing_of_comp_idempotent_of_nondegenerate
-- name    : GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:38:35.676018+00:00
-- url     : https://prove2.me/theorems/83c5feee-e9e2-4541-a8a0-ea87c197d826
-- title:
--   T: exists representing of comp idempotent of nondegenerate
-- statement:
--   The T construction uses the exists representing of comp idempotent of nondegenerate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FunctionalFixedByIdempotentRepresentedStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FunctionalFixedByIdempotentRepresentedStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FunctionalFixedByIdempotentRepresented
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FunctionalFixedByIdempotentRepresentedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ), (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → ∀ (P P' : Module.End ℂ V), P ∘ₗ P = P → FiniteDimensional ℂ (LinearMap.range P) → (∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) → ∀ f : V →ₗ[ℂ] ℂ, f ∘ₗ P = f → ∃ ψ, ∀ φ, B φ ψ = f φ := by sorry
