-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_Stages_stage_snd
-- name    : GlobalTheory.SmGL.Stages.stage_snd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:14:02.826293+00:00
-- url     : https://prove2.me/theorems/a3b506c6-abef-4884-a3ad-3e3acf9487a6
-- title:
--   Stages: stage snd
-- statement:
--   The Stages construction uses the stage snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L307-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L307-L321

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

theorem GlobalTheory.SmGL.Stages.stage_snd (e : a ⊕ bc ≃ n) (f : b ⊕ c ≃ bc) {R : Subgroup (GL n k)} (hRQ : R ≤ parab k (two e))
    (hR : ∀ q : parab k (two e), (q : GL n k) ∈ R ↔ (pr e q).2 ∈ parab k (two f))
    (σ : Representation ℂ (parab k (two f)) V₁) (π : Representation ℂ (GL a k) V₂)
    (ρ : Representation ℂ R W) (i : V₁ ⊗[ℂ] V₂ ≃ₗ[ℂ] W)
    (hi : ∀ (q : parab k (two e)) (h : (q : GL n k) ∈ R) z,
      ρ ⟨q, h⟩ (i z) = i (TensorProduct.map (σ ⟨(pr e q).2, (hR q).1 h⟩) (tauFst e π q) z)) :
    Nonempty ((smInd _ (dat e (extTensor π (smInd _ σ)))).Equiv (smInd R ρ)) := by sorry
