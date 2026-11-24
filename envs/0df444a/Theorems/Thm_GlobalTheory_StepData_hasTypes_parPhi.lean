-- Prove2me | Theorems.Thm_GlobalTheory_StepData_hasTypes_parPhi
-- name    : GlobalTheory.StepData.hasTypes_parPhi
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:51:18.833796+00:00
-- url     : https://prove2.me/theorems/3cae8ead-a834-409c-8ddf-8ad75130ca11
-- title:
--   Step Data: has Types par Phi
-- statement:
--   The Step Data construction uses the has Types par Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1124-L1135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1124-L1135

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
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s']
  {δ : kˣ →* ℂˣ}

theorem GlobalTheory.StepData.hasTypes_parPhi (hδ : IsTame δ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) :
    HasTypes (ν * δ) (parahoric r s' δ hδ).toLevel (parahoric r s δ hδ).toLevel (parPhi δ) := by sorry
