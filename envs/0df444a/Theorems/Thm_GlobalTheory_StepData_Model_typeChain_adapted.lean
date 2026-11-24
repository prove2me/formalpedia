-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Model_typeChain_adapted
-- name    : GlobalTheory.StepData.Model.typeChain_adapted
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:24.462064+00:00
-- url     : https://prove2.me/theorems/2bdca2e8-be2a-4ab4-b007-ef2136deecb6
-- title:
--   Model: type Chain adapted
-- statement:
--   The Model construction uses the type Chain adapted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L217-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L217-L273

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
omit [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.StepData.Model.typeChain_adapted {ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) {s : ℕ} (P : TypeDatum k (κ ⊕ Fin (s + 1)))
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (A : RepFam k s (XIx κ t))
    (hA : (typeChain t ϖ P μ hμ).RepsInStab A) :
    (typeChain t ϖ P μ hμ).Adapted A (box _ ϖ⁻¹) (box _ 1) := by sorry
