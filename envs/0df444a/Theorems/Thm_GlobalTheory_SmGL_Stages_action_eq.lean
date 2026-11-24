-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_Stages_action_eq
-- name    : GlobalTheory.SmGL.Stages.action_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:03.354075+00:00
-- url     : https://prove2.me/theorems/3208fdb6-e0ba-4b0e-a6d0-567754eba28e
-- title:
--   Stages: action eq
-- statement:
--   The Stages construction uses the action eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L323-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L323-L369

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c ab bc n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype ab] [DecidableEq ab] [Fintype bc] [DecidableEq bc] [Fintype n] [DecidableEq n]
  {W V₁ V₂ V₃ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]

theorem GlobalTheory.SmGL.Stages.action_eq (e₁ : ab ⊕ c ≃ n) (f₁ : a ⊕ b ≃ ab) (e₂ : a ⊕ bc ≃ n) (f₂ : b ⊕ c ≃ bc)
    (Ha : ∀ i, e₁ (.inl (f₁ (.inl i))) = e₂ (.inl i))
    (Hb : ∀ i, e₁ (.inl (f₁ (.inr i))) = e₂ (.inr (f₂ (.inl i))))
    (Hc : ∀ i, e₁ (.inr i) = e₂ (.inr (f₂ (.inr i))))
    (π₁ : Representation ℂ (GL a k) V₁) (π₂ : Representation ℂ (GL b k) V₂)
    (π₃ : Representation ℂ (GL c k) V₃) (q₁ : parab k (two e₁)) (q₂ : parab k (two e₂))
    (p₁ : parab k (two f₁)) (p₂ : parab k (two f₂)) (hq : (q₁ : GL n k) = q₂)
    (hp₁ : (pr e₁ q₁).1 = p₁) (hp₂ : (pr e₂ q₂).2 = p₂) (z : (V₂ ⊗[ℂ] V₃) ⊗[ℂ] V₁) :
    TensorProduct.map (dat f₁ (extTensor π₁ π₂) p₁) (tauSnd e₁ π₃ q₁)
        ((TensorProduct.assoc ℂ V₁ V₂ V₃).symm (TensorProduct.comm ℂ _ _ z)) =
      (TensorProduct.assoc ℂ V₁ V₂ V₃).symm (TensorProduct.comm ℂ _ _
        (TensorProduct.map (dat f₂ (extTensor π₂ π₃) p₂) (tauFst e₂ π₁ q₂) z)) := by sorry
