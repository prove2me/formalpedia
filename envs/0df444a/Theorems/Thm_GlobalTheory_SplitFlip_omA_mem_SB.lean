-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_omA_mem_SB
-- name    : GlobalTheory.SplitFlip.omA_mem_SB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:46.337633+00:00
-- url     : https://prove2.me/theorems/c8a54cd4-ffd0-4bc8-8040-98af80ad01c8
-- title:
--   Split Flip: om A mem SB
-- statement:
--   The Split Flip construction uses the om A mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L243-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L243-L245

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

theorem GlobalTheory.SplitFlip.omA_mem_SB (ν β : kˣ →* ℂˣ) (g : GL A k) (h : GL D k) {Φ : Matrix A D k → ℂ}
    (hΦ : Φ ∈ SB (Matrix A D k)) : omA ν β g h Φ ∈ SB (Matrix A D k) := by sorry
