-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_IsRightTranslationIsometric_inv
-- name    : GlobalTheory.SplitFlip.IsRightTranslationIsometric.inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:51.219485+00:00
-- url     : https://prove2.me/theorems/d114c5bd-fb70-43c8-9b89-535124164523
-- title:
--   Is Right Translation Isometric: inv
-- statement:
--   The Is Right Translation Isometric construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L92-L94

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

theorem GlobalTheory.SplitFlip.IsRightTranslationIsometric.inv {ϖ : kˣ} {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {e : ℕ} (h : IsRightTranslationIsometric ϖ ψ α β e) :
    IsRightTranslationIsometric ϖ ψ⁻¹ α β e := by sorry
