-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_invFourierSum_empty
-- name    : GlobalTheory.SplitFlip.invFourierSum_empty
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:13.576031+00:00
-- url     : https://prove2.me/theorems/11b8c2df-467a-5aaa-9700-355dc70e8dd9
-- title:
--   Split Flip: inv Fourier Sum empty
-- statement:
--   The Split Flip construction uses the inv Fourier Sum empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L673-L677
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L673-L677

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

theorem GlobalTheory.SplitFlip.invFourierSum_empty (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (Φ : Matrix A D k → ℂ) :
    invFourierSum ψ ϖ e ∅ Φ = Φ := by sorry
