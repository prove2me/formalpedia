-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Model_typeChain_principal_entry_ne_zero
-- name    : GlobalTheory.StepData.Model.typeChain_principal_entry_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:47.313804+00:00
-- url     : https://prove2.me/theorems/0a81c9e2-32d9-5622-ad4f-625ee6fe7493
-- title:
--   Model: type Chain principal entry ne zero
-- statement:
--   The Model construction uses the type Chain principal entry ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L201-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L201-L213

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
variable [MeasurableSpace k] [BorelSpace k] {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.Model.typeChain_principal_entry_ne_zero {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] {ϖ : kˣ} (hϖ : ∀ z : k, valuation k z < 1 → valuation k z ≤ valuation k (ϖ : k)) (s c : ℕ)
    (h : 0 + 1 + c = s) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    (typeChain t ϖ (TypeDatum.principal k (κ ⊕ Fin (s + 1))) μ hμ).entry ψ ν 0 c h 1 1 ≠ 0 := by sorry
