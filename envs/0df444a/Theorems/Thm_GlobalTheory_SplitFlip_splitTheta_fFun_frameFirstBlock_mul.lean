-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_splitTheta_fFun_frameFirstBlock_mul
-- name    : GlobalTheory.SplitFlip.splitTheta_fFun_frameFirstBlock_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:19.454824+00:00
-- url     : https://prove2.me/theorems/945eba08-1d1c-411b-b2cf-1858b983a160
-- title:
--   Split Flip: split Theta f Fun frame First Block mul
-- statement:
--   The Split Flip construction uses the split Theta f Fun frame First Block mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L790-L796
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L790-L796

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
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitFlip.splitTheta_fFun_frameFirstBlock_mul (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ)
    (Ψ : Matrix A' D k → ℂ) (h : GL D k) : fFun μ σ ν Ψ (X0 k σ * (invT h).val) =
      (ν (gdet h) : ℂ) * apow (gdet h) ((Fintype.card D : ℂ) / 2) * smallF μ ν Ψ (Y0 k σ * h.val) := by sorry
