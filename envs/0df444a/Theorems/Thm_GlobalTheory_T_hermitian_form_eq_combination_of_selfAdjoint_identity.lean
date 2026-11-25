-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitian_form_eq_combination_of_selfAdjoint_identity
-- name    : GlobalTheory.T.hermitian_form_eq_combination_of_selfAdjoint_identity
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:31.430815+00:00
-- url     : https://prove2.me/theorems/754c0669-0748-4ac0-a3a9-3e4d6c79ab77
-- title:
--   T: hermitian form eq combination of self Adjoint identity
-- statement:
--   The T construction uses the hermitian form eq combination of self Adjoint identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianFormEqCombinationOfSelfAdjointIdentityStatement.lean#L6-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianFormEqCombinationOfSelfAdjointIdentityStatement.lean#L6-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFormEqCombinationOfSelfAdjointIdentity
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFormEqCombinationOfSelfAdjointIdentityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitian_form_eq_combination_of_selfAdjoint_identity : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    (∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w)) →
    ∀ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ),
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) →
    ∀ z w : Fin g → ℂ, z ⬝ᵥ H₁.mulVec (star w) = (c₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) +
      ∑ i, (c i : ℂ) * (Polynomial.aeval γ (p i) z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (p i) w))) := by sorry
