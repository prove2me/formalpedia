-- Prove2me | Theorems.Thm_GlobalTheory_StepData_normalBasis_val
-- name    : GlobalTheory.StepData.normalBasis_val
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:44.211668+00:00
-- url     : https://prove2.me/theorems/383dac46-cdc4-4319-b59e-071d0cd7cfd7
-- title:
--   Step Data: normal Basis val
-- statement:
--   The Step Data construction uses the normal Basis val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L625-L630
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L625-L630

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

theorem GlobalTheory.StepData.normalBasis_val (ϖ : kˣ) (e : Fin c → ℤ) (z : n → k) : (normalBasis ϖ e z).val =
    fromBlocks 1 (Matrix.of fun r i => if i.val = 0 then z r * (ϖ : k) ^ e i else 0) 0
      (diagonal fun i => (ϖ : k) ^ e i) := by sorry
