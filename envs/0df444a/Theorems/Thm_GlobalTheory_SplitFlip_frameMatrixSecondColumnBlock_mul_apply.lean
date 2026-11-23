-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_frameMatrixSecondColumnBlock_mul_apply
-- name    : GlobalTheory.SplitFlip.frameMatrixSecondColumnBlock_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:38.820911+00:00
-- url     : https://prove2.me/theorems/677d9b7a-def7-4092-b6d0-62de7b11a974
-- title:
--   Split Flip: frame Matrix Second Column Block mul apply
-- statement:
--   The Split Flip construction uses the frame Matrix Second Column Block mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L272-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L272-L273

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
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']

theorem GlobalTheory.SplitFlip.frameMatrixSecondColumnBlock_mul_apply {B : Type*} (σ : A ⊕ A' ≃ D) (M : Matrix D B k) (i : A') (j : B) :
    (Y0 k σ * M) i j = M (σ (Sum.inr i)) j := by sorry
