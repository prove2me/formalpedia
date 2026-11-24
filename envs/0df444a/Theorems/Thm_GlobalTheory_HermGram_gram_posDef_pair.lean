-- Prove2me | Theorems.Thm_GlobalTheory_HermGram_gram_posDef_pair
-- name    : GlobalTheory.HermGram.gram_posDef_pair
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:19:17.723445+00:00
-- url     : https://prove2.me/theorems/6d305594-0495-45c7-b21a-a4081416f19b
-- title:
--   Herm Gram: gram pos Def pair
-- statement:
--   The Herm Gram construction uses the gram pos Def pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosDefRealGramPairHermitianForms.lean#L59-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosDefRealGramPairHermitianForms.lean#L59-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefRealGramPairHermitianForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.HermGram

theorem GlobalTheory.HermGram.gram_posDef_pair (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (p₁ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re)
    (p₂ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hγ : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) :
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by sorry
