-- Prove2me | Theorems.Thm_GlobalTheory_DetAdResultant_toMatrix_ad
-- name    : GlobalTheory.DetAdResultant.toMatrix_ad
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:57.138409+00:00
-- url     : https://prove2.me/theorems/b93a9847-39c5-4213-9d0c-f185a98f4f1f
-- title:
--   Det Ad Resultant: to Matrix ad
-- statement:
--   The Det Ad Resultant construction uses the to Matrix ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetCommutatorMapEqCharpolyResultant.lean#L45-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetCommutatorMapEqCharpolyResultant.lean#L45-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetCommutatorMapEqCharpolyResultant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
open GlobalTheory GlobalTheory.DetAdResultant

theorem GlobalTheory.DetAdResultant.toMatrix_ad {E : Type} [Field E] {V₁ V₂ : Type} [AddCommGroup V₁] [Module E V₁]
    [AddCommGroup V₂] [Module E V₂] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (b₁ : Module.Basis ι₁ E V₁) (b₂ : Module.Basis ι₂ E V₂)
    (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂) :
    LinearMap.toMatrix (b₂.linearMap b₁) (b₂.linearMap b₁)
        (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) =
      Matrix.reindex (Equiv.prodComm ι₂ ι₁) (Equiv.prodComm ι₂ ι₁)
        ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix (LinearMap.toMatrix b₂ b₂ f₂).transpose).map
          (aeval (LinearMap.toMatrix b₁ b₁ f₁)).toRingHom)) := by sorry
