-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_smallF_mul_left
-- name    : GlobalTheory.SplitFlip.smallF_mul_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:28:41.14782+00:00
-- url     : https://prove2.me/theorems/9bedd92f-485e-4815-b4d9-56d48dfdeb77
-- title:
--   Split Flip: small F mul left
-- statement:
--   The Split Flip construction uses the small F mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L744-L753
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L744-L753

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
omit [DecidableEq D]

theorem GlobalTheory.SplitFlip.smallF_mul_left (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ)
    (g₀ : GL A' k) (Y : Matrix A' D k) :
    (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card D : ℂ) / 2) * smallF μ ν Ψ (g₀.val * Y) = smallF μ ν Ψ Y := by sorry
