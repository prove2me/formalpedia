-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_injective_of_lTensor_conj
-- name    : GroundTheory.GroupCoh.injective_of_lTensor_conj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:32:05.648502+00:00
-- url     : https://prove2.me/theorems/64476b0f-1821-4217-ad0d-f14163af3c23
-- title:
--   Group Coh: injective of l Tensor conj
-- statement:
--   The Group Coh construction uses the injective of l Tensor conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L181-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L181-L188

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}
variable {A B : Rep.{u} k G}
variable {W P₁ P₂ Q₁ Q₂ : Type u} [AddCommGroup W] [Module k W] [Module.Flat k W]
  [AddCommGroup P₁] [Module k P₁] [AddCommGroup P₂] [Module k P₂]
  [AddCommGroup Q₁] [Module k Q₁] [AddCommGroup Q₂] [Module k Q₂]

theorem GroundTheory.GroupCoh.injective_of_lTensor_conj (φ : P₁ →ₗ[k] P₂) (ψ : Q₁ →ₗ[k] Q₂)
    (hψ : Function.Injective ψ) (e₁ : P₁ ≃ₗ[k] TensorProduct k W Q₁)
    (e₂ : P₂ ≃ₗ[k] TensorProduct k W Q₂) (h : ∀ x, e₂ (φ x) = LinearMap.lTensor W ψ (e₁ x)) :
    Function.Injective φ := by sorry
