-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Grid_IsGood_condLE_kappa
-- name    : GlobalTheory.SplitFlip.Grid.IsGood.condLE_kappa
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:04.748191+00:00
-- url     : https://prove2.me/theorems/93d3f569-3518-4f3c-afb2-98983886cdfb
-- title:
--   Is Good: cond LE kappa
-- statement:
--   The Is Good construction uses the cond LE kappa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1118-L1128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1118-L1128

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

theorem GlobalTheory.SplitFlip.Grid.IsGood.condLE_kappa {G : Grid k} {ϖ : kˣ} {ψ : AddChar k Circle} {e : ℕ} (h : G.IsGood ϖ ψ e)
    {b : Edge} (hb : b.InGrid G.m) (X : ℕ × ℕ) : CondLE ϖ e (G.kappa b X) := by sorry
