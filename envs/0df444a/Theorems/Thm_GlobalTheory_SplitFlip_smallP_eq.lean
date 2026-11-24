-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_smallP_eq
-- name    : GlobalTheory.SplitFlip.smallP_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:28:40.335322+00:00
-- url     : https://prove2.me/theorems/5fe675ff-1157-4c38-95b7-42055ea37c93
-- title:
--   Split Flip: small P eq
-- statement:
--   The Split Flip construction uses the small P eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L738-L740
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L738-L740

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
omit [BorelSpace k] [Fintype A] [DecidableEq A]

theorem GlobalTheory.SplitFlip.smallP_eq (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ν α : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (h : GL D k) :
    smallP μ σ ν α Ψ h = smallF μ ν (omB ν α 1 h Ψ) (Y0 k σ) := by sorry
