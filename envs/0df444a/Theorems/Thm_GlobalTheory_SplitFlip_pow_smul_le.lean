-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_pow_smul_le
-- name    : GlobalTheory.SplitFlip.pow_smul_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:20:43.589314+00:00
-- url     : https://prove2.me/theorems/19884b2e-8599-424a-969f-9b5eea30bb73
-- title:
--   Split Flip: pow smul le
-- statement:
--   The Split Flip construction uses the pow smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L539-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L539-L545

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
omit [Fintype D] [DecidableEq D]

theorem GlobalTheory.SplitFlip.pow_smul_le {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (Λ : Submodule 𝒪[k] (D → k)) : ϖ ^ e • Λ ≤ Λ := by sorry
