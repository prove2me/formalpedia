-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_IsCoeffRing_inv
-- name    : GlobalTheory.SplitFlip.IsCoeffRing.inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:50.49425+00:00
-- url     : https://prove2.me/theorems/269ee4c6-8dfd-4899-99f5-12b0d02e4c5e
-- title:
--   Is Coeff Ring: inv
-- statement:
--   The Is Coeff Ring construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L96-L98

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

theorem GlobalTheory.SplitFlip.IsCoeffRing.inv {ϖ : kˣ} {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {e : ℕ} {R : Subring ℂ}
    (h : IsCoeffRing ϖ ψ α β e R) : IsCoeffRing ϖ ψ⁻¹ α β e R := by sorry
