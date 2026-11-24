-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_pairCols_eq_trace
-- name    : GlobalTheory.SplitFlip.pairCols_eq_trace
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:15:53.044632+00:00
-- url     : https://prove2.me/theorems/72794ec2-7604-4a96-870f-f17db638c1d7
-- title:
--   Split Flip: pair Cols eq trace
-- statement:
--   The Split Flip construction uses the pair Cols eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L591-L593
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L591-L593

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
variable [DecidableEq D]
variable [Fintype A]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D]

theorem GlobalTheory.SplitFlip.pairCols_eq_trace (P : Finset D) (Y : Matrix A D k) (T : Matrix A P k) :
    pairCols P Y T = trace (T * (Y.submatrix id (Subtype.val : P → D))ᵀ) := by sorry
