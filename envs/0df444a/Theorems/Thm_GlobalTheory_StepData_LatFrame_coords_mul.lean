-- Prove2me | Theorems.Thm_GlobalTheory_StepData_LatFrame_coords_mul
-- name    : GlobalTheory.StepData.LatFrame.coords_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:27.536393+00:00
-- url     : https://prove2.me/theorems/0854b5c6-109f-4b61-b5cf-c049dda4fabf
-- title:
--   Lat Frame: coords mul
-- statement:
--   The Lat Frame construction uses the coords mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L506-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L506-L514

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
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
open GlobalTheory.StepData.LatFrame

theorem GlobalTheory.StepData.LatFrame.coords_mul (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (h : GL ι k) (g : GL ι' k) (x : Matrix Y Y' k) :
    F.coords F' ((F.conj h).val * x * (F'.conj g).val) = h.val * F.coords F' x * g.val := by sorry
