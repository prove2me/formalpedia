-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_mem_glLat
-- name    : GlobalTheory.SplitFlip.mem_glLat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:35.019071+00:00
-- url     : https://prove2.me/theorems/20f96a3a-bc5e-55c3-b33a-05eba7a69e9d
-- title:
--   Split Flip: mem gl Lat
-- statement:
--   The Split Flip construction uses the mem gl Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L442-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L442-L442

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
variable [DecidableEq D]

theorem GlobalTheory.SplitFlip.mem_glLat {Λ : Submodule 𝒪[k] (D → k)} {h : GL D k} : h ∈ glLat Λ ↔ ∀ x, x ᵥ* h.val ∈ Λ ↔ x ∈ Λ := by sorry
