-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Model_coords_surjective
-- name    : GlobalTheory.StepData.Model.coords_surjective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:02:18.091849+00:00
-- url     : https://prove2.me/theorems/8135e5e0-19f2-4cb6-9675-5612265629ea
-- title:
--   Model: coords surjective
-- statement:
--   The Model construction uses the coords surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L281-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L281-L285

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
variable {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.StepData.Model.coords_surjective {ι ι' Y Y' : Type*} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') : Function.Surjective (F.coords F') := by sorry
