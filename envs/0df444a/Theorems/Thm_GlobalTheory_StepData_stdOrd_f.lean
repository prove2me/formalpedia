-- Prove2me | Theorems.Thm_GlobalTheory_StepData_stdOrd_f
-- name    : GlobalTheory.StepData.stdOrd_f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:11.928182+00:00
-- url     : https://prove2.me/theorems/7c8e1639-b3e8-4755-b150-c4565781c9b7
-- title:
--   Step Data: std Ord f
-- statement:
--   The Step Data construction uses the std Ord f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L664-L667
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L664-L667

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

theorem GlobalTheory.StepData.stdOrd_f (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) (i : Fin j) :
    stdOrd κ t j c h (.inl (.inr ⟨c + i.val, by omega⟩)) = .inl (.inl (.inr i)) := by sorry
