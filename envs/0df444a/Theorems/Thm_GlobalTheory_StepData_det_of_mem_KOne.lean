-- Prove2me | Theorems.Thm_GlobalTheory_StepData_det_of_mem_KOne
-- name    : GlobalTheory.StepData.det_of_mem_KOne
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:22:13.625906+00:00
-- url     : https://prove2.me/theorems/c375cd2e-7f0f-4a9a-91f8-bb632bcb9d58
-- title:
--   Step Data: det of mem KOne
-- statement:
--   The Step Data construction uses the det of mem KOne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L109-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L109-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
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
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.StepData.det_of_mem_KOne {g : GL n k} (h : g ∈ KOne k n) :
    valuation k (((Matrix.GeneralLinearGroup.det g : kˣ) : k) - 1) < 1 := by sorry
