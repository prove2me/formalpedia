-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Model_typeChain_coupIdx
-- name    : GlobalTheory.StepData.Model.typeChain_coupIdx
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:37.957227+00:00
-- url     : https://prove2.me/theorems/885c0162-0089-4473-9b02-93323ac4ae51
-- title:
--   Model: type Chain coup Idx
-- statement:
--   The Model construction uses the type Chain coup Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L287-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L287-L303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.Model.typeChain_coupIdx {ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) {s : ℕ} (P : TypeDatum k (κ ⊕ Fin (s + 1)))
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (A : RepFam k s (XIx κ t))
    (hA : (typeChain t ϖ P μ hμ).RepsInStab A) (h1 : 1 ∈ A s 0 rfl) :
    ∃ yb ∈ (typeChain t ϖ P μ hμ).coupIdx A (box _ ϖ⁻¹) (box _ 1),
      (typeChain t ϖ P μ hμ).xiPen (box _ 1) 1 yb ≠ 0 := by sorry
