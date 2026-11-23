-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_mem_diagLat
-- name    : GlobalTheory.SplitFlip.mem_diagLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:55.599123+00:00
-- url     : https://prove2.me/theorems/5ac8e6e7-62f7-4f89-9d3d-3205b9cbef7f
-- title:
--   Split Flip: mem diag Lat
-- statement:
--   The Split Flip construction uses the mem diag Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L341-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L341-L342

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

theorem GlobalTheory.SplitFlip.mem_diagLat {c : D → kˣ} {x : D → k} :
    x ∈ diagLat c ↔ ∀ j, valuation k (x j) ≤ valuation k (c j : k) := by sorry
