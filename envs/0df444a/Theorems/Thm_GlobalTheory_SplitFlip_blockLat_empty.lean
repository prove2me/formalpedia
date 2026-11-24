-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_blockLat_empty
-- name    : GlobalTheory.SplitFlip.blockLat_empty
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:19:56.369573+00:00
-- url     : https://prove2.me/theorems/c37c070d-a19c-4ab1-a421-4477af6792b2
-- title:
--   Split Flip: block Lat empty
-- statement:
--   The Split Flip construction uses the block Lat empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L511-L512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L511-L512

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
variable {A D : Type*}
variable [Fintype D]
variable [DecidableEq D]
omit [Fintype D]

theorem GlobalTheory.SplitFlip.blockLat_empty (ϖ : kˣ) (e : ℕ) : blockLat ϖ e (∅ : Finset D) = stdLat k D := by sorry
