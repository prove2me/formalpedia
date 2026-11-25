-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_invFourierSum_inv_eq_neg
-- name    : GlobalTheory.SplitFlip.invFourierSum_inv_eq_neg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:23.616182+00:00
-- url     : https://prove2.me/theorems/4a9284d9-f6fb-57e4-9cd7-800e0c01f34b
-- title:
--   Split Flip: inv Fourier Sum inv eq neg
-- statement:
--   The Split Flip construction uses the inv Fourier Sum inv eq neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L653-L665
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L653-L665

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

theorem GlobalTheory.SplitFlip.invFourierSum_inv_eq_neg (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (Ψ : Matrix A D k → ℂ)
    (T : Matrix A D k) : invFourierSum ψ⁻¹ ϖ e P Ψ T =
      invFourierSum ψ ϖ e P Ψ (setCols P T (Matrix.of fun i j => -T i j)) := by sorry
