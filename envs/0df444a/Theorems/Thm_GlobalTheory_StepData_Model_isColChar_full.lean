-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Model_isColChar_full
-- name    : GlobalTheory.StepData.Model.isColChar_full
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:55.703047+00:00
-- url     : https://prove2.me/theorems/884363ad-c675-4f75-8631-fd7de3200491
-- title:
--   Model: is Col Char full
-- statement:
--   The Model construction uses the is Col Char full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L15-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
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
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem GlobalTheory.StepData.Model.isColChar_full {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) :
    IsColChar ψ (TypeDatum.full k (n ⊕ Fin c)).toLevel 1 1 := by sorry
