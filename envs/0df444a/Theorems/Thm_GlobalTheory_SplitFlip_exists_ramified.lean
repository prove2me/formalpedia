-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_exists_ramified
-- name    : GlobalTheory.SplitFlip.exists_ramified
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:42.817407+00:00
-- url     : https://prove2.me/theorems/abb1b60a-3cc6-416a-b32f-4af8265f39a2
-- title:
--   Split Flip: exists ramified
-- statement:
--   The Split Flip construction uses the exists ramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L119-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L119-L144

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

theorem GlobalTheory.SplitFlip.exists_ramified {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    ∃ ν : kˣ →* ℂˣ, ¬ IsUnram ν ∧ CondLE ϖ 2 ν ∧ ∀ x, ‖(ν x : ℂ)‖ = 1 := by sorry
