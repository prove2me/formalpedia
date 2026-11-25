-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_frameSecondBlock_mul_frameFirstBlock_transpose_eq_zero
-- name    : GlobalTheory.SplitFlip.frameSecondBlock_mul_frameFirstBlock_transpose_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:30.167933+00:00
-- url     : https://prove2.me/theorems/3d84ff54-53c5-47f5-a0fc-81047b324f72
-- title:
--   Split Flip: frame Second Block mul frame First Block transpose eq zero
-- statement:
--   The Split Flip construction uses the frame Second Block mul frame First Block transpose eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L277-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L277-L281

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

theorem GlobalTheory.SplitFlip.frameSecondBlock_mul_frameFirstBlock_transpose_eq_zero (σ : A ⊕ A' ≃ D) (h : GL D k) :
    (Y0 k σ * h.val) * (X0 k σ * (invT h).val)ᵀ = 0 := by sorry
