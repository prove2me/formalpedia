-- Prove2me | Theorems.Thm_GlobalTheory_StepData_mem_stabLat_iff
-- name    : GlobalTheory.StepData.mem_stabLat_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:03.171869+00:00
-- url     : https://prove2.me/theorems/6888aa74-7333-565a-b4e4-ee9b067db11e
-- title:
--   Step Data: mem stab Lat iff
-- statement:
--   The Step Data construction uses the mem stab Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L592-L594
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L592-L594

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
variable [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.StepData.mem_stabLat_iff {g h : GL Y k} : h ∈ stabLat g ↔ latOf (h * g) = latOf g := by sorry
