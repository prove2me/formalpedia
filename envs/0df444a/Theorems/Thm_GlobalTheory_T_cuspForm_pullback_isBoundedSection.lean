-- Prove2me | Theorems.Thm_GlobalTheory_T_cuspForm_pullback_isBoundedSection
-- name    : GlobalTheory.T.cuspForm_pullback_isBoundedSection
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:27.151437+00:00
-- url     : https://prove2.me/theorems/a5f78413-c040-447a-8995-a0f7ce717f20
-- title:
--   T: cusp Form pullback is Bounded Section
-- statement:
--   The T construction uses the cusp Form pullback is Bounded Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormPullbackIsBoundedSectionStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormPullbackIsBoundedSectionStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CuspFormPullbackIsBoundedSection
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CuspFormPullbackIsBoundedSectionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cuspForm_pullback_isBoundedSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → ∀ (h : U) (c : C), (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := by sorry
