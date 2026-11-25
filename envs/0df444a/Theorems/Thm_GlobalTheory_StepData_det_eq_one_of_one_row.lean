-- Prove2me | Theorems.Thm_GlobalTheory_StepData_det_eq_one_of_one_row
-- name    : GlobalTheory.StepData.det_eq_one_of_one_row
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:11:18.446671+00:00
-- url     : https://prove2.me/theorems/5b79e276-78c0-445f-a0bd-abfc89048f50
-- title:
--   Step Data: det eq one of one row
-- statement:
--   The Step Data construction uses the det eq one of one row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedDepthOneLevelCharOfOneRowFirstBlock.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedDepthOneLevelCharOfOneRowFirstBlock.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedDepthOneLevelCharOfOneRowFirstBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.StepData

theorem GlobalTheory.StepData.det_eq_one_of_one_row {k n : Type*} [Field k] [Fintype n] [DecidableEq n] (M : Matrix n n k) (i : n)
    (h : ∀ a b, a ≠ i → M a b = (1 : Matrix n n k) a b) (hii : M i i = 1) : M.det = 1 := by sorry
