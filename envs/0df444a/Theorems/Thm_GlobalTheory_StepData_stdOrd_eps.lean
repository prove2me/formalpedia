-- Prove2me | Theorems.Thm_GlobalTheory_StepData_stdOrd_eps
-- name    : GlobalTheory.StepData.stdOrd_eps
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:25.633833+00:00
-- url     : https://prove2.me/theorems/6642e03f-3056-4c8e-9eb4-5a6882ffceb2
-- title:
--   Step Data: std Ord eps
-- statement:
--   The Step Data construction uses the std Ord eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L656-L657
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L656-L657

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

theorem GlobalTheory.StepData.stdOrd_eps (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) (i : κ) :
    stdOrd κ t j c h (.inl (.inl i)) = .inl (.inl (.inl i)) := by sorry
