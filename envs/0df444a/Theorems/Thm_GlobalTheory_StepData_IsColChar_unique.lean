-- Prove2me | Theorems.Thm_GlobalTheory_StepData_IsColChar_unique
-- name    : GlobalTheory.StepData.IsColChar.unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:36.339102+00:00
-- url     : https://prove2.me/theorems/189c3f57-ea25-4705-b225-27bfc0a44999
-- title:
--   Is Col Char: unique
-- statement:
--   The Is Col Char construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L704-L708
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L704-L708

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
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.StepData.IsColChar.unique {ψ : AddChar k Circle} {P : Level (GL (n ⊕ Fin c) k)} {h : GL (n ⊕ Fin c) k}
    {χ χ' : prX (Cgrp P.J h) →* ℂˣ} (H : IsColChar ψ P h χ) (H' : IsColChar ψ P h χ') : χ = χ' := by sorry
