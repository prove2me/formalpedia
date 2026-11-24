-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_omA_mul
-- name    : GlobalTheory.SplitFlip.omA_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:52.755264+00:00
-- url     : https://prove2.me/theorems/dde57e41-cb55-452e-99ee-2dca60238c16
-- title:
--   Split Flip: om A mul
-- statement:
--   The Split Flip construction uses the om A mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L225-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L225-L227

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

theorem GlobalTheory.SplitFlip.omA_mul (ν β : kˣ →* ℂˣ) (g g' : GL A k) (h h' : GL D k) (Φ : Matrix A D k → ℂ) :
    omA ν β (g * g') (h * h') Φ = omA ν β g h (omA ν β g' h' Φ) := by sorry
