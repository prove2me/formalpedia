-- Prove2me | Theorems.Thm_GlobalTheory_projMatrix_abstract
-- name    : GlobalTheory.projMatrix_abstract
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:38.089357+00:00
-- url     : https://prove2.me/theorems/94940d9d-08d0-4887-8246-ba6cf8a30b9c
-- title:
--   Global Theory: proj Matrix abstract
-- statement:
--   The Global Theory construction uses the proj Matrix abstract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMatricesOfProjectiveComplex.lean#L7-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMatricesOfProjectiveComplex.lean#L7-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMatricesOfProjectiveComplex
import Theorems.Thm_GlobalTheory_IsGradedMap_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory

theorem GlobalTheory.projMatrix_abstract {S : Type} [CommRing S] {P₀ P₁ P₂ F₀ F₁ G₁ G₂ : Type}
    [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂]
    [AddCommGroup F₀] [Module S F₀] [AddCommGroup F₁] [Module S F₁]
    [AddCommGroup G₁] [Module S G₁] [AddCommGroup G₂] [Module S G₂]
    (d₀ : P₀ →ₗ[S] P₁) (d₁ : P₁ →ₗ[S] P₂) (p₀ : F₀ →ₗ[S] P₀) (s₀ : P₀ →ₗ[S] F₀)
    (p₁ : F₁ →ₗ[S] P₁) (s₁ : P₁ →ₗ[S] F₁) (D₀ : F₀ →ₗ[S] G₁) (D₁ : G₁ →ₗ[S] G₂)
    (q₁ : G₁ →ₗ[S] F₁) (q₀ : G₁ →ₗ[S] F₀) (i₁ : F₁ →ₗ[S] G₁) (i₀ : F₀ →ₗ[S] G₁)
    (r₂ : G₂ →ₗ[S] P₂) (r₁ : G₂ →ₗ[S] F₁) (r₀ : G₂ →ₗ[S] P₀)
    (h₀ : p₀ ∘ₗ s₀ = LinearMap.id) (h₁ : p₁ ∘ₗ s₁ = LinearMap.id)
    (hq₁ : q₁ ∘ₗ D₀ = s₁ ∘ₗ d₀ ∘ₗ p₀) (hq₀ : q₀ ∘ₗ D₀ = LinearMap.id - s₀ ∘ₗ p₀)
    (hi : i₁ ∘ₗ q₁ + i₀ ∘ₗ q₀ = LinearMap.id)
    (hr₂ : r₂ ∘ₗ D₁ = d₁ ∘ₗ p₁ ∘ₗ q₁) (hr₁ : r₁ ∘ₗ D₁ = q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁)
    (hr₀ : r₀ ∘ₗ D₁ = p₀ ∘ₗ q₀) :
    Set.BijOn p₀ {v | D₀ v = 0} (LinearMap.ker d₀) ∧
      (Function.Exact d₀ d₁ → ∀ w, D₁ w = 0 → ∃ v, D₀ v = w) := by sorry
