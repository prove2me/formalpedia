-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_maximalIdeal_eq
-- name    : GlobalTheory.SplitFlip.IsUnif.maximalIdeal_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:18.647112+00:00
-- url     : https://prove2.me/theorems/7f114417-27a0-4178-8725-6927a926fb1e
-- title:
--   Is Unif: maximal Ideal eq
-- statement:
--   The Is Unif construction uses the maximal Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L107-L113

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

theorem GlobalTheory.SplitFlip.IsUnif.maximalIdeal_eq {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {(⟨ϖ, hϖ.mem⟩ : 𝒪[k])} := by sorry
