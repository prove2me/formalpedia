-- Prove2me | Theorems.Thm_GlobalTheory_StepData_mem_latOf_typeFrame
-- name    : GlobalTheory.StepData.mem_latOf_typeFrame
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:50:09.610639+00:00
-- url     : https://prove2.me/theorems/71d014cb-cd8f-4a2c-8780-618d0474fcac
-- title:
--   Step Data: mem lat Of type Frame
-- statement:
--   The Step Data construction uses the mem lat Of type Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L632-L644
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L632-L644

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
variable {k : Type*} [Field k] {ι n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.StepData.mem_latOf_typeFrame [ValuativeRel k] (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (y : n ⊕ Fin c → k) :
    y ∈ latOf (typeFrame ϖ ord).bas ↔ (∀ i, y (.inl i) ∈ 𝒪[k]) ∧
      ∀ i : Fin c, valuation k (y (.inr i)) ≤ valuation k ((ϖ : k) ^ (i.val + 1)) := by sorry
