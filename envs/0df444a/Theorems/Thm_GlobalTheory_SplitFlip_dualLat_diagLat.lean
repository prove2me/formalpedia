-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_dualLat_diagLat
-- name    : GlobalTheory.SplitFlip.dualLat_diagLat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:20:13.805797+00:00
-- url     : https://prove2.me/theorems/33f179f2-c685-421c-8d06-0bb5afe72b10
-- title:
--   Split Flip: dual Lat diag Lat
-- statement:
--   The Split Flip construction uses the dual Lat diag Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L397-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L397-L414

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

theorem GlobalTheory.SplitFlip.dualLat_diagLat (c : D → kˣ) : dualLat (diagLat c) = diagLat fun j => (c j)⁻¹ := by sorry
