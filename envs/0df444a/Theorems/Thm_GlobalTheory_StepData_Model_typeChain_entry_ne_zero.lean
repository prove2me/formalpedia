-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Model_typeChain_entry_ne_zero
-- name    : GlobalTheory.StepData.Model.typeChain_entry_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:29.271518+00:00
-- url     : https://prove2.me/theorems/9af3acd0-f0b5-4c03-bb78-5c3bdf81aac3
-- title:
--   Model: type Chain entry ne zero
-- statement:
--   The Model construction uses the type Chain entry ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L124-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L124-L199

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

theorem GlobalTheory.StepData.Model.typeChain_entry_ne_zero (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (s c : ℕ)
    (h : 0 + 1 + c = s) (P : TypeDatum k (κ ⊕ Fin (s + 1))) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hP : ∀ g : P.J, (P.rho (μ 1) g : ℂ) =
      ψ (∑ i : Fin s, (g : GL (κ ⊕ Fin (s + 1)) k).val (.inr i.castSucc) (.inr i.succ) / ϖ)) :
    DoubleCoset.mk _ _ 1 ∈ (typeChain t ϖ P μ hμ).idx ψ ν 0 c h 1 ∧
      (typeChain t ϖ P μ hμ).entry ψ ν 0 c h 1 1 ≠ 0 := by sorry
