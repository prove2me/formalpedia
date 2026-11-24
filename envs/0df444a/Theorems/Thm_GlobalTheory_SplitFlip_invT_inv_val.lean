-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_invT_inv_val
-- name    : GlobalTheory.SplitFlip.invT_inv_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:01.635486+00:00
-- url     : https://prove2.me/theorems/326ecab1-bf8b-419d-84dc-cee3550fe443
-- title:
--   Split Flip: inv T inv val
-- statement:
--   The Split Flip construction uses the inv T inv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L172-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L172-L172

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
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SplitFlip.invT_inv_val (h : GL D k) : ((invT h)⁻¹).val = h.valᵀ := by sorry
