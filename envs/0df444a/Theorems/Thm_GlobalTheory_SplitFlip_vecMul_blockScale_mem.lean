-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_vecMul_blockScale_mem
-- name    : GlobalTheory.SplitFlip.vecMul_blockScale_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:20:53.474805+00:00
-- url     : https://prove2.me/theorems/a7e22148-ca2e-419a-b212-d58779765788
-- title:
--   Split Flip: vec Mul block Scale mem
-- statement:
--   The Split Flip construction uses the vec Mul block Scale mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L501-L507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L501-L507

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

theorem GlobalTheory.SplitFlip.vecMul_blockScale_mem (ϖ : kˣ) (e : ℕ) (P : Finset D) (x : D → k) :
    x ᵥ* (blockScale ϖ e P).val ∈ blockLat ϖ e P ↔ x ∈ stdLat k D := by sorry
