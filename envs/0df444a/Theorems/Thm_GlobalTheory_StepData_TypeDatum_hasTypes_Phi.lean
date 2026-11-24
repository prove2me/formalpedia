-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_hasTypes_Phi
-- name    : GlobalTheory.StepData.TypeDatum.hasTypes_Phi
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:11.635287+00:00
-- url     : https://prove2.me/theorems/fccebf50-fcfe-47b4-bbce-fbc6d6cf2eaa
-- title:
--   Type Datum: has Types Phi
-- statement:
--   The Type Datum construction uses the has Types Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1061-L1068
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1061-L1068

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
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
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open GlobalTheory.StepData.TypeDatum
variable (P : TypeDatum k a) {μ : kˣ →* ℂˣ}

theorem GlobalTheory.StepData.TypeDatum.hasTypes_Phi (hμ : IsTame μ) : HasTypes μ P.toLevel (P.step t μ hμ).toLevel (P.Phi t μ) := by sorry
