-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_omB_mem_SB
-- name    : GlobalTheory.SplitFlip.omB_mem_SB
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:18.888353+00:00
-- url     : https://prove2.me/theorems/2ab81df0-850f-44b6-8846-887ed4fbe57d
-- title:
--   Split Flip: om B mem SB
-- statement:
--   The Split Flip construction uses the om B mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L247-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L247-L249

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

theorem GlobalTheory.SplitFlip.omB_mem_SB (ν α : kˣ →* ℂˣ) (g : GL A' k) (h : GL D k) {Ψ : Matrix A' D k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix A' D k)) : omB ν α g h Ψ ∈ SB (Matrix A' D k) := by sorry
