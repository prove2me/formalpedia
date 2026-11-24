-- Prove2me | Theorems.Thm_GlobalTheory_StepData_LatFrame_om_transport
-- name    : GlobalTheory.StepData.LatFrame.om_transport
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:49:54.662024+00:00
-- url     : https://prove2.me/theorems/f34dee1f-44b5-4eee-808c-609b462b7ab2
-- title:
--   Lat Frame: om transport
-- statement:
--   The Lat Frame construction uses the om transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L518-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L518-L523

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
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
open GlobalTheory.StepData.LatFrame
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.StepData.LatFrame.om_transport (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (μ : kˣ →* ℂˣ) (g : GL ι' k) (h : GL ι k)
    (Φ : Matrix ι ι' k → ℂ) :
    om μ (F'.conj g) (F.conj h) (F.transport F' Φ) = F.transport F' (om μ g h Φ) := by sorry
