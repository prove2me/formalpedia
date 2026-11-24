-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Level_mem_map
-- name    : GlobalTheory.StepData.Level.mem_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:48:19.64861+00:00
-- url     : https://prove2.me/theorems/c4d454b0-3b67-4d2b-a2af-afcb6b0da2dd
-- title:
--   Level: mem map
-- statement:
--   The Level construction uses the mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L21-L22

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

theorem GlobalTheory.StepData.Level.mem_map {G G' : Type*} [Group G] [Group G'] {φ : G ≃* G'} {P : Level G} {h : G'} :
    h ∈ (P.map φ).J ↔ φ.symm h ∈ P.J := by sorry
