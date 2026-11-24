-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_shellSum_smul
-- name    : GlobalTheory.SplitFlip.shellSum_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:28:12.412424+00:00
-- url     : https://prove2.me/theorems/c562b1ea-f7ec-4208-8e88-4e69a85aecff
-- title:
--   Split Flip: shell Sum smul
-- statement:
--   The Split Flip construction uses the shell Sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L725-L727
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L725-L727

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
variable [MeasurableSpace k] [BorelSpace k]
omit [BorelSpace k]

theorem GlobalTheory.SplitFlip.shellSum_smul {a : ℕ} (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (z c : ℂ)
    (φ : Matrix (Fin a) (Fin a) k → ℂ) : shellSum μ ϖ ν z (fun g => c * φ g) = c * shellSum μ ϖ ν z φ := by sorry
