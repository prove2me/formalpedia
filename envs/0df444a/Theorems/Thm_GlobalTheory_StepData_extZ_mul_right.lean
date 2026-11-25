-- Prove2me | Theorems.Thm_GlobalTheory_StepData_extZ_mul_right
-- name    : GlobalTheory.StepData.extZ_mul_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:51.458817+00:00
-- url     : https://prove2.me/theorems/44db54dc-4a46-58e7-9e1a-f3160dc0b25b
-- title:
--   Step Data: ext Z mul right
-- statement:
--   The Step Data construction uses the ext Z mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1006-L1008
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1006-L1008

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

theorem GlobalTheory.StepData.extZ_mul_right (J : Subgroup (GL a k)) (ρ : J →* ℂˣ) (g g' : J) :
    extZ J ρ ((g : GL a k).val * (g' : GL a k).val) = extZ J ρ (g : GL a k).val * ρ g' := by sorry
