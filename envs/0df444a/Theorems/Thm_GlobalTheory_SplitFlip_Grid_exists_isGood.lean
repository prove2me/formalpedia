-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Grid_exists_isGood
-- name    : GlobalTheory.SplitFlip.Grid.exists_isGood
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:45.899108+00:00
-- url     : https://prove2.me/theorems/109465b4-0888-4ca5-925f-bfdf6cc44fdf
-- title:
--   Grid: exists is Good
-- statement:
--   The Grid construction uses the exists is Good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L980-L984
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L980-L984

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
open GlobalTheory.SplitFlip.Grid
variable (G : Grid k)

theorem GlobalTheory.SplitFlip.Grid.exists_isGood (m r t s : ℕ) (ht : Odd t) (hs : Odd s) : ∃ (G : Grid k) (ϖ : kˣ) (ψ : AddChar k Circle),
    G.m = m ∧ G.r = r ∧ G.t = t ∧ G.s = s ∧ G.IsGood ϖ ψ 2 := by sorry
