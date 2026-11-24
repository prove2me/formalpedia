-- Prove2me | Theorems.Thm_GlobalTheory_StepData_standardOrderExtendedBasis_apply_low_block
-- name    : GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:44.361209+00:00
-- url     : https://prove2.me/theorems/1fbc68c8-1f68-4340-85ff-cc4914e54a21
-- title:
--   Step Data: standard Order Extended Basis apply low block
-- statement:
--   The Step Data construction uses the standard Order Extended Basis apply low block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L659-L662
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L659-L662

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

theorem GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) (i : Fin c) :
    stdOrd κ t j c h (.inl (.inr ⟨i.val, by omega⟩)) = .inr i := by sorry
