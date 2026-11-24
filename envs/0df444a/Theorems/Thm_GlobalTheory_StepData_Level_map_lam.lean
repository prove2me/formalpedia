-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Level_map_lam
-- name    : GlobalTheory.StepData.Level.map_lam
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:50:28.034523+00:00
-- url     : https://prove2.me/theorems/428127aa-f904-4ec2-86b8-93eca9c9c777
-- title:
--   Level: map lam
-- statement:
--   The Level construction uses the map lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L24-L25

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

theorem GlobalTheory.StepData.Level.map_lam {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (P : Level G) (h : (P.map φ).J) :
    (P.map φ).lam h = P.lam ⟨φ.symm h, h.2⟩ := by sorry
