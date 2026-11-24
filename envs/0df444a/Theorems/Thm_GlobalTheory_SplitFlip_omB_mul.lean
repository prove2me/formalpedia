-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_omB_mul
-- name    : GlobalTheory.SplitFlip.omB_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:58.405683+00:00
-- url     : https://prove2.me/theorems/4db9f8f2-679e-4fcb-bcf0-3e540fd0096b
-- title:
--   Split Flip: om B mul
-- statement:
--   The Split Flip construction uses the om B mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L229-L231

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

theorem GlobalTheory.SplitFlip.omB_mul (ν α : kˣ →* ℂˣ) (g g' : GL A' k) (h h' : GL D k) (Ψ : Matrix A' D k → ℂ) :
    omB ν α (g * g') (h * h') Ψ = omB ν α g h (omB ν α g' h' Ψ) := by sorry
