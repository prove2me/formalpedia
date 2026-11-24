-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_mem_smul_lat
-- name    : GlobalTheory.SplitFlip.mem_smul_lat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:48.734868+00:00
-- url     : https://prove2.me/theorems/537f16aa-970f-4b95-87aa-2b09fd13dc5d
-- title:
--   Split Flip: mem smul lat
-- statement:
--   The Split Flip construction uses the mem smul lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L319-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L319-L321

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

theorem GlobalTheory.SplitFlip.mem_smul_lat (c : kˣ) (Λ : Submodule 𝒪[k] (D → k)) (x : D → k) : x ∈ c • Λ ↔ c⁻¹ • x ∈ Λ := by sorry
