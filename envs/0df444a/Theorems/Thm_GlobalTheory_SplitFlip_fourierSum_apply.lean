-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_fourierSum_apply
-- name    : GlobalTheory.SplitFlip.fourierSum_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:19.724804+00:00
-- url     : https://prove2.me/theorems/39b9abc5-8d22-43d0-b016-0e34564b0096
-- title:
--   Split Flip: fourier Sum apply
-- statement:
--   The Split Flip construction uses the fourier Sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L633-L636
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L633-L636

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

theorem GlobalTheory.SplitFlip.fourierSum_apply (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (Φ : Matrix A D k → ℂ)
    (Y : Matrix A D k) : fourierSum ψ ϖ e P Φ Y = if ∀ i, ∀ j ∈ P, ((ϖ ^ e : kˣ) : k) * Y i j ∈ 𝒪[k] then
    ((resCard k : ℂ) ^ (e * Fintype.card A * P.card))⁻¹ *
      ∑ T : A → P → Res k e, Φ (setCols P Y (liftRes T)) * (ψ (pairCols P Y (liftRes T)) : ℂ) else 0 := by sorry
