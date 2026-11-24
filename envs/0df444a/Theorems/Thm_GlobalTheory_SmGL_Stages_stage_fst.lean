-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_Stages_stage_fst
-- name    : GlobalTheory.SmGL.Stages.stage_fst
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:13:56.847085+00:00
-- url     : https://prove2.me/theorems/14cccff7-259a-49d9-b8c8-b42e85e0e058
-- title:
--   Stages: stage fst
-- statement:
--   The Stages construction uses the stage fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L291-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L291-L305

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

theorem GlobalTheory.SmGL.Stages.stage_fst (e : ab ⊕ c ≃ n) (f : a ⊕ b ≃ ab) {R : Subgroup (GL n k)} (hRQ : R ≤ parab k (two e))
    (hR : ∀ q : parab k (two e), (q : GL n k) ∈ R ↔ (pr e q).1 ∈ parab k (two f))
    (σ : Representation ℂ (parab k (two f)) V₁) (π : Representation ℂ (GL c k) V₂)
    (ρ : Representation ℂ R W) (i : V₁ ⊗[ℂ] V₂ ≃ₗ[ℂ] W)
    (hi : ∀ (q : parab k (two e)) (h : (q : GL n k) ∈ R) z,
      ρ ⟨q, h⟩ (i z) = i (TensorProduct.map (σ ⟨(pr e q).1, (hR q).1 h⟩) (tauSnd e π q) z)) :
    Nonempty ((smInd _ (dat e (extTensor (smInd _ σ) π))).Equiv (smInd R ρ)) := by sorry
