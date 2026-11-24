-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_mem_dualLat
-- name    : GlobalTheory.SplitFlip.mem_dualLat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:20:30.199956+00:00
-- url     : https://prove2.me/theorems/9b8f6a05-d01b-4a40-bf10-f308e36af2f8
-- title:
--   Split Flip: mem dual Lat
-- statement:
--   The Split Flip construction uses the mem dual Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L392-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L392-L395

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
variable [Fintype D]

theorem GlobalTheory.SplitFlip.mem_dualLat {Λ : Submodule 𝒪[k] (D → k)} {x : D → k} : x ∈ dualLat Λ ↔ ∀ y ∈ Λ, x ⬝ᵥ y ∈ 𝒪[k] := by sorry
