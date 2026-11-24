-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Grid_isTensor_pureTensor
-- name    : GlobalTheory.SplitFlip.Grid.isTensor_pureTensor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:45.96047+00:00
-- url     : https://prove2.me/theorems/493107d2-f93e-4fe2-8ea3-71a9bd607800
-- title:
--   Grid: is Tensor pure Tensor
-- statement:
--   The Grid construction uses the is Tensor pure Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1020-L1026
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1020-L1026

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
open GlobalTheory.SplitFlip.Grid
variable (G : Grid k)

theorem GlobalTheory.SplitFlip.Grid.isTensor_pureTensor (ϖ : kˣ) (e : ℕ) (γ : List Edge)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (hφ : ∀ b ∈ γ, IsNatDatum ϖ e (φ b)) :
    G.IsTensor ϖ e γ (G.lines₂ γ φ) := by sorry
