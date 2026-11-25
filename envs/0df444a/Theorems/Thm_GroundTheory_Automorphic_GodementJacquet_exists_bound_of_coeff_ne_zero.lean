-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_exists_bound_of_coeff_ne_zero
-- name    : GroundTheory.Automorphic.GodementJacquet.exists_bound_of_coeff_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:23.28527+00:00
-- url     : https://prove2.me/theorems/3c584f5f-92c6-5c45-8688-2c425b8fd372
-- title:
--   Godement Jacquet: exists bound of coeff ne zero
-- statement:
--   The Godement Jacquet construction uses the exists bound of coeff ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLeviSupport.lean#L18-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLeviSupport.lean#L18-L149

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLeviSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic ValuativeRel
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem GroundTheory.Automorphic.GodementJacquet.exists_bound_of_coeff_ne_zero (hσ : IsSmooth σ) (hc : IsCuspidal σ) (w : W)
    {ℓ : Module.Dual ℂ W} (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) :
    ∃ N : ℕ, ∀ (μ : Fin n → ℤ) (k₁ k₂ : levi F n β), (k₁ : GL (Fin n) F) ∈ integralGL F n →
      (k₂ : GL (Fin n) F) ∈ integralGL F n →
      ℓ (σ (k₁ * ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ * k₂) w) ≠ 0 →
      ∃ c : Fin n → ℤ, (∀ i j, β i = β j → c i = c j) ∧ ∀ i, c i ≤ μ i ∧ μ i ≤ c i + N := by sorry
