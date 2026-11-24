-- Prove2me | Theorems.Thm_GlobalTheory_exists_free_step
-- name    : GlobalTheory.exists_free_step
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:32:22.853802+00:00
-- url     : https://prove2.me/theorems/8184382c-877c-42a5-a1df-c59901bed782
-- title:
--   Global Theory: exists free step
-- statement:
--   The Global Theory construction uses the exists free step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L255-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L255-L297

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem GlobalTheory.exists_free_step {C₀ C₁ K₁ K₂ : Type*} [AddCommGroup C₀] [AddCommGroup C₁]
    [AddCommGroup K₁] [AddCommGroup K₂] [Module R C₀] [Module R C₁] [Module R K₁] [Module R K₂]
    [Module.Finite R K₁] (d : C₀ →ₗ[R] C₁) (φ : K₁ →ₗ[R] C₁) (δ : K₁ →ₗ[R] K₂) (B : Submodule R C₀)
    [Module.Finite R (LinearMap.ker d ⧸ B.comap (LinearMap.ker d).subtype)] :
    ∃ (m : ℕ) (φ₀ : (Fin m → R) →ₗ[R] C₀) (δ₀ : (Fin m → R) →ₗ[R] K₁),
      (∀ x, d (φ₀ x) = φ (δ₀ x)) ∧ (∀ x, δ (δ₀ x) = 0) ∧
      ∀ c k, d c = φ k → δ k = 0 → ∃ x, c - φ₀ x ∈ B ∧ δ₀ x = k := by sorry
