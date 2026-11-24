-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_rank_eq_card_iff_exists_frameMatrixFirstColumnBlock
-- name    : GlobalTheory.SplitFlip.rank_eq_card_iff_exists_frameMatrixFirstColumnBlock
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:05.641059+00:00
-- url     : https://prove2.me/theorems/88ffb240-94d2-4fc8-9665-1acb97fea26a
-- title:
--   Split Flip: rank eq card iff exists frame Matrix First Column Block
-- statement:
--   The Split Flip construction uses the rank eq card iff exists frame Matrix First Column Block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L285-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L285-L312

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
omit [DecidableEq A] [DecidableEq A']

theorem GlobalTheory.SplitFlip.rank_eq_card_iff_exists_frameMatrixFirstColumnBlock (σ : A ⊕ A' ≃ D) (X : Matrix A D k) :
    X.rank = Fintype.card A ↔ ∃ h : GL D k, X = X0 k σ * (invT h).val := by sorry
