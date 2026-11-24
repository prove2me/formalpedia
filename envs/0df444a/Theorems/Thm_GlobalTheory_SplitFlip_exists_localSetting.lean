-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_exists_localSetting
-- name    : GlobalTheory.SplitFlip.exists_localSetting
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:20:18.961807+00:00
-- url     : https://prove2.me/theorems/ce780790-d19d-4b1a-88dd-0da81a0ba28c
-- title:
--   Split Flip: exists local Setting
-- statement:
--   The Split Flip construction uses the exists local Setting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L146-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L146-L150

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

theorem GlobalTheory.SplitFlip.exists_localSetting : ∃ (ϖ : kˣ) (ψ : AddChar k Circle) (α : kˣ →* ℂˣ), IsRightTranslationIsometric ϖ ψ α 1 2 := by sorry
