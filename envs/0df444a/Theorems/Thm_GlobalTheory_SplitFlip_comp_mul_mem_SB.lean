-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_comp_mul_mem_SB
-- name    : GlobalTheory.SplitFlip.comp_mul_mem_SB
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:36.903128+00:00
-- url     : https://prove2.me/theorems/d60f791d-a03a-4df1-8e20-e3637b44f677
-- title:
--   Split Flip: comp mul mem SB
-- statement:
--   The Split Flip construction uses the comp mul mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L233-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L233-L241

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

theorem GlobalTheory.SplitFlip.comp_mul_mem_SB (g : GL A k) (h : GL D k) {Φ : Matrix A D k → ℂ} (hΦ : Φ ∈ SB (Matrix A D k)) :
    (fun X => Φ (g.val * X * h.val)) ∈ SB (Matrix A D k) := by sorry
