-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_irreducible
-- name    : GlobalTheory.SplitFlip.IsUnif.irreducible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:32.463405+00:00
-- url     : https://prove2.me/theorems/74a1b54e-47f6-401e-8477-bd8733ea5902
-- title:
--   Is Unif: irreducible
-- statement:
--   The Is Unif construction uses the irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L115-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L115-L117

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

theorem GlobalTheory.SplitFlip.IsUnif.irreducible {ϖ : kˣ} (hϖ : IsUnif ϖ) : Irreducible (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) := by sorry
