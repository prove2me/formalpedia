-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_fourierSum_empty
-- name    : GlobalTheory.SplitFlip.fourierSum_empty
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:22.087864+00:00
-- url     : https://prove2.me/theorems/bd2712fc-a8b7-4d4d-b7fc-a06d862eb084
-- title:
--   Split Flip: fourier Sum empty
-- statement:
--   The Split Flip construction uses the fourier Sum empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L667-L671
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L667-L671

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
variable [DecidableEq A]

theorem GlobalTheory.SplitFlip.fourierSum_empty (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (Φ : Matrix A D k → ℂ) :
    fourierSum ψ ϖ e ∅ Φ = Φ := by sorry
