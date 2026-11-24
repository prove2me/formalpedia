-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_mem_matLat
-- name    : GlobalTheory.SplitFlip.mem_matLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:16.914451+00:00
-- url     : https://prove2.me/theorems/e93377f7-85f2-49a6-b9a6-ebe9e7fa85ba
-- title:
--   Split Flip: mem mat Lat
-- statement:
--   The Split Flip construction uses the mem mat Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L331-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L331-L331

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

theorem GlobalTheory.SplitFlip.mem_matLat {Λ : Submodule 𝒪[k] (D → k)} {X : Matrix A D k} : X ∈ matLat A Λ ↔ ∀ i, X.row i ∈ Λ := by sorry
