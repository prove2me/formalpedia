-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Assignment_read_mem_KO
-- name    : GlobalTheory.SplitFlip.Assignment.read_mem_KO
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:51.651571+00:00
-- url     : https://prove2.me/theorems/2d5fcb8d-1390-4ad6-b9a6-527281e82d8f
-- title:
--   Assignment: read mem KO
-- statement:
--   The Assignment construction uses the read mem KO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1112-L1116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1112-L1116

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

theorem GlobalTheory.SplitFlip.Assignment.read_mem_KO (s : Assignment) {n : Type*} [Fintype n] [DecidableEq n] {g : GL n k}
    (hg : g ∈ KO k n) : s.read g ∈ KO k n := by sorry
