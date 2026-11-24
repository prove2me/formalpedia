-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_hasDepth_indicator
-- name    : GlobalTheory.SplitFlip.hasDepth_indicator
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:41.741704+00:00
-- url     : https://prove2.me/theorems/629eb8f0-189a-4bf9-9f48-f49186c24d22
-- title:
--   Split Flip: has Depth indicator
-- statement:
--   The Split Flip construction uses the has Depth indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L547-L553
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L547-L553

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
omit [Fintype D] [DecidableEq D]

theorem GlobalTheory.SplitFlip.hasDepth_indicator {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (Λ : Submodule 𝒪[k] (D → k)) :
    HasDepth ϖ e Λ ((matLat A Λ : Set (Matrix A D k)).indicator 1) := by sorry
