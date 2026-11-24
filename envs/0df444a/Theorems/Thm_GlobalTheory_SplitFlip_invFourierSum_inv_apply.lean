-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_invFourierSum_inv_apply
-- name    : GlobalTheory.SplitFlip.invFourierSum_inv_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:20:49.82368+00:00
-- url     : https://prove2.me/theorems/f66a0e42-97ec-4782-8a1a-87e7c7842683
-- title:
--   Split Flip: inv Fourier Sum inv apply
-- statement:
--   The Split Flip construction uses the inv Fourier Sum inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L647-L651
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L647-L651

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
open Classical

theorem GlobalTheory.SplitFlip.invFourierSum_inv_apply (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (Ψ : Matrix A D k → ℂ)
    (T : Matrix A D k) : invFourierSum ψ⁻¹ ϖ e P Ψ T = if ∀ i, ∀ j ∈ P, T i j ∈ 𝒪[k] then
    ∑ S : A → P → Res k e, Ψ (setCols P T ((ϖ ^ e)⁻¹ • liftRes S)) *
      (ψ (pairCols P T ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) else 0 := by sorry
