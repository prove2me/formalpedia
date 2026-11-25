-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_compl_block_two
-- name    : GlobalTheory.SplitFlip.compl_block_two
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:25:36.319302+00:00
-- url     : https://prove2.me/theorems/d3e22501-16e2-5ed9-9e61-2522e32339dc
-- title:
--   Split Flip: compl block two
-- statement:
--   The Split Flip construction uses the compl block two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L863-L864
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L863-L864

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D₁ D₂ : Type*} [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]

theorem GlobalTheory.SplitFlip.compl_block_two : (Assignment.two.block D₁ D₂)ᶜ = Assignment.one.block D₁ D₂ := by sorry
