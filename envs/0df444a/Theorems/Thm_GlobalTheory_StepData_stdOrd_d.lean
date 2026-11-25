-- Prove2me | Theorems.Thm_GlobalTheory_StepData_stdOrd_d
-- name    : GlobalTheory.StepData.stdOrd_d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:54.329828+00:00
-- url     : https://prove2.me/theorems/04c207dd-7456-4c67-a25d-c751675e8875
-- title:
--   Step Data: std Ord d
-- statement:
--   The Step Data construction uses the std Ord d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L669-L670
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L669-L670

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

theorem GlobalTheory.StepData.stdOrd_d (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) (p : Fin j × t) :
    stdOrd κ t j c h (.inr p) = .inl (.inr p) := by sorry
