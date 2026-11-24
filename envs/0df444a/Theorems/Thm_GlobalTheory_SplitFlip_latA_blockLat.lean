-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_latA_blockLat
-- name    : GlobalTheory.SplitFlip.latA_blockLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:01.213079+00:00
-- url     : https://prove2.me/theorems/916b3ac5-208d-45ec-aed9-07a70535daf4
-- title:
--   Split Flip: lat A block Lat
-- statement:
--   The Split Flip construction uses the lat A block Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L518-L522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L518-L522

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

theorem GlobalTheory.SplitFlip.latA_blockLat (ϖ : kˣ) (e : ℕ) (P : Finset D) : latA ϖ e (blockLat ϖ e P) = blockLat ϖ e Pᶜ := by sorry
